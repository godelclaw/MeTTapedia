import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 16. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block16 :
    ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) =
      expectedPermutationSign 16 := by
  decide

theorem signedAxisTrace_certificate_block16 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 16 reflectionMask) =
        expectedSignedAxisTrace 16 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 16 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block16 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 16 reflectionMask) =
        expectedOrientationSign 16 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 16 0
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 16 1
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 16 2
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 16 3
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 16 4
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 16 5
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 16 6
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 16 7
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 16 8
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 16 9
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 16 10
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 16 11
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 16 12
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 16 13
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 16 14
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 16) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 16 15
    rw [permutationSign_certificate_block16]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block16 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 16 rank =
        expectedReflectionCharacterMoment parity 16 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block16,
      orientationSign_certificate_block16,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
