import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 0. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block0 :
    ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) =
      expectedPermutationSign 0 := by
  decide

theorem signedAxisTrace_certificate_block0 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 0 reflectionMask) =
        expectedSignedAxisTrace 0 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((1 : ℚ) + 1) + 1) + 1 = expectedSignedAxisTrace 0 0
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + 1) + 1 = expectedSignedAxisTrace 0 1
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + 1) + 1 = expectedSignedAxisTrace 0 2
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + 1) + 1 = expectedSignedAxisTrace 0 3
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 1) + (-1)) + 1 = expectedSignedAxisTrace 0 4
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + (-1)) + 1 = expectedSignedAxisTrace 0 5
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + (-1)) + 1 = expectedSignedAxisTrace 0 6
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + (-1)) + 1 = expectedSignedAxisTrace 0 7
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 1) + 1) + (-1) = expectedSignedAxisTrace 0 8
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + 1) + (-1) = expectedSignedAxisTrace 0 9
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + 1) + (-1) = expectedSignedAxisTrace 0 10
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + 1) + (-1) = expectedSignedAxisTrace 0 11
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 1) + (-1)) + (-1) = expectedSignedAxisTrace 0 12
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 1) + (-1)) + (-1) = expectedSignedAxisTrace 0 13
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + (-1)) + (-1)) + (-1) = expectedSignedAxisTrace 0 14
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + (-1)) + (-1)) + (-1) = expectedSignedAxisTrace 0 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block0 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 0 reflectionMask) =
        expectedOrientationSign 0 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 0 0
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 0 1
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 0 2
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 0 3
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 0 4
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 0 5
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 0 6
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 0 7
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 0 8
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 0 9
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 0 10
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 0 11
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 0 12
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 0 13
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 0 14
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 0) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 0 15
    rw [permutationSign_certificate_block0]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block0 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 0 rank =
        expectedReflectionCharacterMoment parity 0 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block0,
      orientationSign_certificate_block0,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
