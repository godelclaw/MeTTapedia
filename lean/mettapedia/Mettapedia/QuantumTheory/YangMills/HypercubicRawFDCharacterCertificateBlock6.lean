import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 6. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block6 :
    ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) =
      expectedPermutationSign 6 := by
  decide

theorem signedAxisTrace_certificate_block6 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 6 reflectionMask) =
        expectedSignedAxisTrace 6 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 1) + 1 = expectedSignedAxisTrace 6 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 1 = expectedSignedAxisTrace 6 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 1 = expectedSignedAxisTrace 6 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 1 = expectedSignedAxisTrace 6 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 1 = expectedSignedAxisTrace 6 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 1 = expectedSignedAxisTrace 6 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 1 = expectedSignedAxisTrace 6 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 1 = expectedSignedAxisTrace 6 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + (-1) = expectedSignedAxisTrace 6 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + (-1) = expectedSignedAxisTrace 6 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + (-1) = expectedSignedAxisTrace 6 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + (-1) = expectedSignedAxisTrace 6 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + (-1) = expectedSignedAxisTrace 6 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + (-1) = expectedSignedAxisTrace 6 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + (-1) = expectedSignedAxisTrace 6 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + (-1) = expectedSignedAxisTrace 6 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block6 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 6 reflectionMask) =
        expectedOrientationSign 6 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 6 0
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 6 1
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 6 2
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 6 3
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 6 4
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 6 5
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 6 6
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 6 7
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 6 8
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 6 9
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 6 10
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 6 11
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 6 12
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 6 13
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 6 14
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 6) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 6 15
    rw [permutationSign_certificate_block6]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block6 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 6 rank =
        expectedReflectionCharacterMoment parity 6 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block6,
      orientationSign_certificate_block6,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
