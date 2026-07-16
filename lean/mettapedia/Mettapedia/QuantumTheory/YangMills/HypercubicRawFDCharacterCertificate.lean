import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock0
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock1
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock2
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock3
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock4
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock5
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock6
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock7
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock8
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock9
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock10
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock11
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock12
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock13
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock14
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock15
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock16
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock17
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock18
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock19
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock20
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock21
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock22
import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterCertificateBlock23

/-! # Complete kernel-checked raw `F,D` character certificate -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate (permutation : Fin 24) :
    ((Equiv.Perm.sign (permutationCode permutation) : ℤ) : ℚ) =
      expectedPermutationSign permutation := by
  fin_cases permutation
  · exact permutationSign_certificate_block0
  · exact permutationSign_certificate_block1
  · exact permutationSign_certificate_block2
  · exact permutationSign_certificate_block3
  · exact permutationSign_certificate_block4
  · exact permutationSign_certificate_block5
  · exact permutationSign_certificate_block6
  · exact permutationSign_certificate_block7
  · exact permutationSign_certificate_block8
  · exact permutationSign_certificate_block9
  · exact permutationSign_certificate_block10
  · exact permutationSign_certificate_block11
  · exact permutationSign_certificate_block12
  · exact permutationSign_certificate_block13
  · exact permutationSign_certificate_block14
  · exact permutationSign_certificate_block15
  · exact permutationSign_certificate_block16
  · exact permutationSign_certificate_block17
  · exact permutationSign_certificate_block18
  · exact permutationSign_certificate_block19
  · exact permutationSign_certificate_block20
  · exact permutationSign_certificate_block21
  · exact permutationSign_certificate_block22
  · exact permutationSign_certificate_block23

theorem signedAxisTrace_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    signedAxisTrace
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      expectedSignedAxisTrace permutation reflectionMask := by
  fin_cases permutation
  · exact signedAxisTrace_certificate_block0 reflectionMask
  · exact signedAxisTrace_certificate_block1 reflectionMask
  · exact signedAxisTrace_certificate_block2 reflectionMask
  · exact signedAxisTrace_certificate_block3 reflectionMask
  · exact signedAxisTrace_certificate_block4 reflectionMask
  · exact signedAxisTrace_certificate_block5 reflectionMask
  · exact signedAxisTrace_certificate_block6 reflectionMask
  · exact signedAxisTrace_certificate_block7 reflectionMask
  · exact signedAxisTrace_certificate_block8 reflectionMask
  · exact signedAxisTrace_certificate_block9 reflectionMask
  · exact signedAxisTrace_certificate_block10 reflectionMask
  · exact signedAxisTrace_certificate_block11 reflectionMask
  · exact signedAxisTrace_certificate_block12 reflectionMask
  · exact signedAxisTrace_certificate_block13 reflectionMask
  · exact signedAxisTrace_certificate_block14 reflectionMask
  · exact signedAxisTrace_certificate_block15 reflectionMask
  · exact signedAxisTrace_certificate_block16 reflectionMask
  · exact signedAxisTrace_certificate_block17 reflectionMask
  · exact signedAxisTrace_certificate_block18 reflectionMask
  · exact signedAxisTrace_certificate_block19 reflectionMask
  · exact signedAxisTrace_certificate_block20 reflectionMask
  · exact signedAxisTrace_certificate_block21 reflectionMask
  · exact signedAxisTrace_certificate_block22 reflectionMask
  · exact signedAxisTrace_certificate_block23 reflectionMask

theorem orientationSign_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    Hypercubic4.orientationSign
        (decodedHypercubicCharacterElement permutation reflectionMask) =
      expectedOrientationSign permutation reflectionMask := by
  fin_cases permutation
  · exact orientationSign_certificate_block0 reflectionMask
  · exact orientationSign_certificate_block1 reflectionMask
  · exact orientationSign_certificate_block2 reflectionMask
  · exact orientationSign_certificate_block3 reflectionMask
  · exact orientationSign_certificate_block4 reflectionMask
  · exact orientationSign_certificate_block5 reflectionMask
  · exact orientationSign_certificate_block6 reflectionMask
  · exact orientationSign_certificate_block7 reflectionMask
  · exact orientationSign_certificate_block8 reflectionMask
  · exact orientationSign_certificate_block9 reflectionMask
  · exact orientationSign_certificate_block10 reflectionMask
  · exact orientationSign_certificate_block11 reflectionMask
  · exact orientationSign_certificate_block12 reflectionMask
  · exact orientationSign_certificate_block13 reflectionMask
  · exact orientationSign_certificate_block14 reflectionMask
  · exact orientationSign_certificate_block15 reflectionMask
  · exact orientationSign_certificate_block16 reflectionMask
  · exact orientationSign_certificate_block17 reflectionMask
  · exact orientationSign_certificate_block18 reflectionMask
  · exact orientationSign_certificate_block19 reflectionMask
  · exact orientationSign_certificate_block20 reflectionMask
  · exact orientationSign_certificate_block21 reflectionMask
  · exact orientationSign_certificate_block22 reflectionMask
  · exact orientationSign_certificate_block23 reflectionMask

theorem reflectionCharacterMoment_certificate
    (parity : ContractionParity) (permutation : Fin 24) (rank : Fin 17) :
    encodedReflectionCharacterMoment parity permutation rank =
      expectedReflectionCharacterMoment parity permutation rank := by
  fin_cases permutation
  · exact reflectionCharacterMoment_certificate_block0 parity rank
  · exact reflectionCharacterMoment_certificate_block1 parity rank
  · exact reflectionCharacterMoment_certificate_block2 parity rank
  · exact reflectionCharacterMoment_certificate_block3 parity rank
  · exact reflectionCharacterMoment_certificate_block4 parity rank
  · exact reflectionCharacterMoment_certificate_block5 parity rank
  · exact reflectionCharacterMoment_certificate_block6 parity rank
  · exact reflectionCharacterMoment_certificate_block7 parity rank
  · exact reflectionCharacterMoment_certificate_block8 parity rank
  · exact reflectionCharacterMoment_certificate_block9 parity rank
  · exact reflectionCharacterMoment_certificate_block10 parity rank
  · exact reflectionCharacterMoment_certificate_block11 parity rank
  · exact reflectionCharacterMoment_certificate_block12 parity rank
  · exact reflectionCharacterMoment_certificate_block13 parity rank
  · exact reflectionCharacterMoment_certificate_block14 parity rank
  · exact reflectionCharacterMoment_certificate_block15 parity rank
  · exact reflectionCharacterMoment_certificate_block16 parity rank
  · exact reflectionCharacterMoment_certificate_block17 parity rank
  · exact reflectionCharacterMoment_certificate_block18 parity rank
  · exact reflectionCharacterMoment_certificate_block19 parity rank
  · exact reflectionCharacterMoment_certificate_block20 parity rank
  · exact reflectionCharacterMoment_certificate_block21 parity rank
  · exact reflectionCharacterMoment_certificate_block22 parity rank
  · exact reflectionCharacterMoment_certificate_block23 parity rank

theorem encodedCharacterMoment_certificate
    (parity : ContractionParity) (rank : Fin 17) :
    encodedCharacterMoment parity rank =
      expectedTotalCharacterMoment parity rank := by
  unfold encodedCharacterMoment
  simp_rw [reflectionCharacterMoment_certificate]
  cases parity <;> fin_cases rank <;>
    norm_num [expectedReflectionCharacterMoment,
      expectedTotalCharacterMoment, Fin.sum_univ_succ]

theorem expectedTotalCharacterMoment_eq_multiplicity
    (parity : ContractionParity) (rank : Fin 17) :
    expectedTotalCharacterMoment parity rank =
      384 * certifiedTensorInvariantMultiplicity parity rank := by
  cases parity <;> fin_cases rank <;>
    norm_num [expectedTotalCharacterMoment,
      certifiedTensorInvariantMultiplicity]

theorem rawTensorInvariantCharacterMultiplicity_certificate
    (parity : ContractionParity) (rank : Fin 17) :
    rawTensorInvariantCharacterMultiplicity parity rank =
      certifiedTensorInvariantMultiplicity parity rank := by
  unfold rawTensorInvariantCharacterMultiplicity
  rw [hypercubic_character_sum_eq_encoded,
    encodedCharacterMoment_certificate,
    expectedTotalCharacterMoment_eq_multiplicity]
  ring

theorem finrank_axisTensorInvariantSubmodule_certificate
    (parity : ContractionParity) (rank : Fin 17) :
    Module.finrank ℚ (axisTensorInvariantSubmodule parity rank) =
      certifiedTensorInvariantMultiplicity parity rank := by
  apply Nat.cast_injective (R := ℚ)
  rw [finrank_axisTensorInvariantSubmodule,
    rawTensorInvariantCharacterMultiplicity_certificate]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
