import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 3. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block3 :
    ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) =
      expectedPermutationSign 3 := by
  decide

theorem signedAxisTrace_certificate_block3 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 3 reflectionMask) =
        expectedSignedAxisTrace 3 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 0
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 1
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 2
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 3
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 4
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 5
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 6
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 7
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 8
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 9
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 10
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 11
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 12
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 13
    norm_num [expectedSignedAxisTrace]
  · change (((1 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 14
    norm_num [expectedSignedAxisTrace]
  · change ((((-1) : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 3 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block3 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 3 reflectionMask) =
        expectedOrientationSign 3 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 3 0
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 3 1
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 3 2
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 3 3
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 3 4
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 3 5
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 3 6
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 3 7
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 3 8
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 3 9
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 3 10
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 3 11
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 3 12
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 3 13
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 3 14
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 3) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 3 15
    rw [permutationSign_certificate_block3]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block3 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 3 rank =
        expectedReflectionCharacterMoment parity 3 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block3,
      orientationSign_certificate_block3,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
