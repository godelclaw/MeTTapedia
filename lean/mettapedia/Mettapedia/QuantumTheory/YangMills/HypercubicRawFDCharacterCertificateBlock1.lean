import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 1. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block1 :
    ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) =
      expectedPermutationSign 1 := by
  decide

theorem signedAxisTrace_certificate_block1 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 1 reflectionMask) =
        expectedSignedAxisTrace 1 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((1 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 0
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 1
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 2
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 3
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 4
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 5
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 6
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 7
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 8
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 9
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 10
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 11
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 12
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + 0) + 0 = expectedSignedAxisTrace 1 13
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 14
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + 0) + 0 = expectedSignedAxisTrace 1 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block1 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 1 reflectionMask) =
        expectedOrientationSign 1 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 1 0
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 1 1
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 1 2
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 1 3
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 1 4
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 1 5
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 1 6
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 1 7
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 1 8
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 1 9
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 1 10
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 1 11
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 1 12
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 1 13
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 1 14
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 1) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 1 15
    rw [permutationSign_certificate_block1]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block1 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 1 rank =
        expectedReflectionCharacterMoment parity 1 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block1,
      orientationSign_certificate_block1,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
