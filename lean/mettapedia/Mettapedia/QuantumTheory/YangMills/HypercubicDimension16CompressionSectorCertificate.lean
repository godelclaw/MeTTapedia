import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock0
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock1
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock2
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock3
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock4
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock5
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock6
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock7
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock8
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock9
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock10
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock11
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock12
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificateBlock13

/-!
# Exact class-compressed dimension-sixteen census

The fourteen power-trace classes reduce the proposed hypercubic Reynolds
expression to exact rational arithmetic.  These certificates establish all
eight field sectors, both contraction parities, and the identity-specialized
cycle-index values.  They do not identify those values with a finite carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus

theorem classCompressedSectorCharacter_certificate
    (traceClass : PowerTraceClass) (fieldIndex : Fin 8) :
    classCompressedSectorCharacter traceClass (fieldIndex.1 + 1) =
      expectedClassCompressedSectorCharacter traceClass
        (fieldIndex.1 + 1) := by
  fin_cases traceClass
  · exact classCompressedSectorCharacter_certificate_block0 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block1 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block2 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block3 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block4 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block5 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block6 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block7 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block8 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block9 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block10 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block11 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block12 fieldIndex
  · exact classCompressedSectorCharacter_certificate_block13 fieldIndex

theorem classCompressedInvariantMultiplicity_certificate
    (parity : ContractionParity) (fieldIndex : Fin 8) :
    classCompressedInvariantMultiplicity parity (fieldIndex.1 + 1) =
      expectedCompressedInvariantMultiplicity parity
        (fieldIndex.1 + 1) := by
  unfold classCompressedInvariantMultiplicity
  simp_rw [classCompressedSectorCharacter_certificate]
  cases parity <;> fin_cases fieldIndex <;>
    norm_num [expectedClassCompressedSectorCharacter,
      expectedCompressedInvariantMultiplicity, classOrientationSign,
      classMultiplicity, Fin.sum_univ_succ]

theorem compressedCarrierCardinality_certificate
    (fieldIndex : Fin 8) :
    compressedCarrierCardinality (fieldIndex.1 + 1) =
      expectedCompressedCarrierCardinality (fieldIndex.1 + 1) := by
  fin_cases fieldIndex <;>
    norm_num (config := { maxSteps := 1000000 })
      [compressedCarrierCardinality, fieldPartitions,
      identityPartitionDerivativeCount, derivativeCountForFields,
      expectedCompressedCarrierCardinality, Finset.sum_range_succ]

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
