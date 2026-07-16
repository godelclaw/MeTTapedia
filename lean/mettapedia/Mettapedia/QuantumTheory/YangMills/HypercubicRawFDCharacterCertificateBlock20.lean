import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 20. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block20 :
    ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) =
      expectedPermutationSign 20 := by
  decide

theorem signedAxisTrace_certificate_block20 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 20 reflectionMask) =
        expectedSignedAxisTrace 20 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 20 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 20 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block20 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 20 reflectionMask) =
        expectedOrientationSign 20 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 20 0
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 20 1
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 20 2
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 20 3
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 20 4
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 20 5
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 20 6
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 20 7
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 20 8
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 20 9
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 20 10
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 20 11
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 20 12
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 20 13
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 20 14
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 20) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 20 15
    rw [permutationSign_certificate_block20]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block20 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 20 rank =
        expectedReflectionCharacterMoment parity 20 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block20,
      orientationSign_certificate_block20,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
