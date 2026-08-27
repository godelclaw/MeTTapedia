import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 4. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block4 :
    ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) =
      expectedPermutationSign 4 := by
  decide

theorem signedAxisTrace_certificate_block4 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 4 reflectionMask) =
        expectedSignedAxisTrace 4 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 0
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 1
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 2
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 3
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 4
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 5
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 6
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 7
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 8
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 9
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 10
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 11
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 12
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 13
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 14
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 4 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block4 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 4 reflectionMask) =
        expectedOrientationSign 4 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 4 0
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 4 1
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 4 2
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 4 3
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 4 4
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 4 5
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 4 6
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 4 7
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 4 8
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 4 9
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 4 10
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 4 11
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 4 12
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 4 13
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 4 14
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 4) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 4 15
    rw [permutationSign_certificate_block4]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block4 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 4 rank =
        expectedReflectionCharacterMoment parity 4 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block4,
      orientationSign_certificate_block4,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
