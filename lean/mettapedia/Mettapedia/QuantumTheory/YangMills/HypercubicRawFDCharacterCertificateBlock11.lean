import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 11. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block11 :
    ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) =
      expectedPermutationSign 11 := by
  decide

theorem signedAxisTrace_certificate_block11 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 11 reflectionMask) =
        expectedSignedAxisTrace 11 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 1) + 0 = expectedSignedAxisTrace 11 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + (-1)) + 0 = expectedSignedAxisTrace 11 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block11 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 11 reflectionMask) =
        expectedOrientationSign 11 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 11 0
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 11 1
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 11 2
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 11 3
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 11 4
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 11 5
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 11 6
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 11 7
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 11 8
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 11 9
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 11 10
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 11 11
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 11 12
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 11 13
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 11 14
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 11) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 11 15
    rw [permutationSign_certificate_block11]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block11 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 11 rank =
        expectedReflectionCharacterMoment parity 11 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block11,
      orientationSign_certificate_block11,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
