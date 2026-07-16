import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 14. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block14 :
    ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) =
      expectedPermutationSign 14 := by
  decide

theorem signedAxisTrace_certificate_block14 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 14 reflectionMask) =
        expectedSignedAxisTrace 14 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 1) + 0) + 1 = expectedSignedAxisTrace 14 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 1 = expectedSignedAxisTrace 14 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 1 = expectedSignedAxisTrace 14 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 1 = expectedSignedAxisTrace 14 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 1 = expectedSignedAxisTrace 14 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + 1 = expectedSignedAxisTrace 14 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 1 = expectedSignedAxisTrace 14 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + 1 = expectedSignedAxisTrace 14 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + (-1) = expectedSignedAxisTrace 14 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + (-1) = expectedSignedAxisTrace 14 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + (-1) = expectedSignedAxisTrace 14 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + (-1) = expectedSignedAxisTrace 14 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + (-1) = expectedSignedAxisTrace 14 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 0) + (-1) = expectedSignedAxisTrace 14 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + (-1) = expectedSignedAxisTrace 14 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 0) + (-1) = expectedSignedAxisTrace 14 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block14 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 14 reflectionMask) =
        expectedOrientationSign 14 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 14 0
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 14 1
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 14 2
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 14 3
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 14 4
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 14 5
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 14 6
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 14 7
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 14 8
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 14 9
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 14 10
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 14 11
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 14 12
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 14 13
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 14 14
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 14) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 14 15
    rw [permutationSign_certificate_block14]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block14 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 14 rank =
        expectedReflectionCharacterMoment parity 14 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block14,
      orientationSign_certificate_block14,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
