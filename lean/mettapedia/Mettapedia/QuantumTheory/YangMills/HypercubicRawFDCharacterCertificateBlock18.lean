import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 18. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block18 :
    ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) =
      expectedPermutationSign 18 := by
  decide

theorem signedAxisTrace_certificate_block18 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 18 reflectionMask) =
        expectedSignedAxisTrace 18 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 18 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block18 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 18 reflectionMask) =
        expectedOrientationSign 18 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 18 0
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 18 1
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 18 2
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 18 3
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 18 4
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 18 5
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 18 6
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 18 7
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 18 8
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 18 9
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 18 10
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 18 11
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 18 12
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 18 13
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 18 14
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 18) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 18 15
    rw [permutationSign_certificate_block18]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block18 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 18 rank =
        expectedReflectionCharacterMoment parity 18 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block18,
      orientationSign_certificate_block18,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
