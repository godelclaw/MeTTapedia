import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 2. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block2 :
    ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) =
      expectedPermutationSign 2 := by
  decide

theorem signedAxisTrace_certificate_block2 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 2 reflectionMask) =
        expectedSignedAxisTrace 2 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((1 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 0
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 1
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 2
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 3
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 4
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 5
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 6
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 1 = expectedSignedAxisTrace 2 7
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 8
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 9
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 10
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 11
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 12
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 13
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 14
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + (-1) = expectedSignedAxisTrace 2 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block2 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 2 reflectionMask) =
        expectedOrientationSign 2 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 2 0
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 2 1
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 2 2
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 2 3
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 2 4
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 2 5
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 2 6
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 2 7
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 2 8
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 2 9
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 2 10
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 2 11
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 2 12
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 2 13
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 2 14
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 2) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 2 15
    rw [permutationSign_certificate_block2]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block2 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 2 rank =
        expectedReflectionCharacterMoment parity 2 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block2,
      orientationSign_certificate_block2,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
