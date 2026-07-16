import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 21. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block21 :
    ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) =
      expectedPermutationSign 21 := by
  decide

theorem signedAxisTrace_certificate_block21 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 21 reflectionMask) =
        expectedSignedAxisTrace 21 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 1) + 1) + 0 = expectedSignedAxisTrace 21 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 1) + 0 = expectedSignedAxisTrace 21 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 1) + 0 = expectedSignedAxisTrace 21 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 1) + 0 = expectedSignedAxisTrace 21 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + (-1)) + 0 = expectedSignedAxisTrace 21 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + (-1)) + 0 = expectedSignedAxisTrace 21 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + (-1)) + 0 = expectedSignedAxisTrace 21 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + (-1)) + 0 = expectedSignedAxisTrace 21 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 1) + 0 = expectedSignedAxisTrace 21 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + 1) + 0 = expectedSignedAxisTrace 21 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 1) + 0 = expectedSignedAxisTrace 21 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + 1) + 0 = expectedSignedAxisTrace 21 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + (-1)) + 0 = expectedSignedAxisTrace 21 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 1) + (-1)) + 0 = expectedSignedAxisTrace 21 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + (-1)) + 0 = expectedSignedAxisTrace 21 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + (-1)) + (-1)) + 0 = expectedSignedAxisTrace 21 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block21 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 21 reflectionMask) =
        expectedOrientationSign 21 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 21 0
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 21 1
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 21 2
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 21 3
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 21 4
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 21 5
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 21 6
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 21 7
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 21 8
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 21 9
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 21 10
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 21 11
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 21 12
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 21 13
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 21 14
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 21) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 21 15
    rw [permutationSign_certificate_block21]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block21 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 21 rank =
        expectedReflectionCharacterMoment parity 21 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block21,
      orientationSign_certificate_block21,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
