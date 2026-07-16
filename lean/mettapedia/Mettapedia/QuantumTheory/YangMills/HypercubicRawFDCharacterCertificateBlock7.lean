import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 7. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block7 :
    ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) =
      expectedPermutationSign 7 := by
  decide

theorem signedAxisTrace_certificate_block7 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 7 reflectionMask) =
        expectedSignedAxisTrace 7 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 7 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block7 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 7 reflectionMask) =
        expectedOrientationSign 7 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 7 0
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 7 1
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 7 2
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 7 3
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 7 4
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 7 5
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 7 6
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 7 7
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 7 8
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 7 9
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 7 10
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 7 11
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 7 12
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 7 13
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 7 14
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 7) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 7 15
    rw [permutationSign_certificate_block7]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block7 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 7 rank =
        expectedReflectionCharacterMoment parity 7 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block7,
      orientationSign_certificate_block7,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
