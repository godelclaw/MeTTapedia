import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 12. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block12 :
    ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) =
      expectedPermutationSign 12 := by
  decide

theorem signedAxisTrace_certificate_block12 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 12 reflectionMask) =
        expectedSignedAxisTrace 12 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 12 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 12 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block12 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 12 reflectionMask) =
        expectedOrientationSign 12 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 12 0
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 12 1
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 12 2
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 12 3
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 12 4
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 12 5
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 12 6
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 12 7
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 12 8
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 12 9
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 12 10
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 12 11
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 12 12
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 12 13
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 12 14
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 12) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 12 15
    rw [permutationSign_certificate_block12]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block12 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 12 rank =
        expectedReflectionCharacterMoment parity 12 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block12,
      orientationSign_certificate_block12,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
