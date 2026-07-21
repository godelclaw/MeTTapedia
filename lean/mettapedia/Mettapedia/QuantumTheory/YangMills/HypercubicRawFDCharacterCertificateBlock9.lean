import Mettapedia.QuantumTheory.YangMills.HypercubicRawFDCharacterGeneratedData

/-! Kernel-checked raw `F,D` character certificate block 9. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicRawFDCharacterCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus

theorem permutationSign_certificate_block9 :
    ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) =
      expectedPermutationSign 9 := by
  decide

theorem signedAxisTrace_certificate_block9 :
    ∀ reflectionMask : Fin 16,
      signedAxisTrace
          (decodedHypercubicCharacterElement 9 reflectionMask) =
        expectedSignedAxisTrace 9 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [signedAxisTrace_four_terms]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 0
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 1
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 2
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 3
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 4
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 5
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 6
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 7
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 8
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 9
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 10
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 11
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 12
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 13
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 14
    norm_num [expectedSignedAxisTrace]
  · change (((0 : ℚ) + 0) + 0) + 0 = expectedSignedAxisTrace 9 15
    norm_num [expectedSignedAxisTrace]

theorem orientationSign_certificate_block9 :
    ∀ reflectionMask : Fin 16,
      Hypercubic4.orientationSign
          (decodedHypercubicCharacterElement 9 reflectionMask) =
        expectedOrientationSign 9 reflectionMask := by
  intro reflectionMask
  fin_cases reflectionMask <;> rw [orientationSign_four_factors]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 9 0
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * 1))) =
      expectedOrientationSign 9 1
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 9 2
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * 1))) =
      expectedOrientationSign 9 3
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 9 4
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * 1))) =
      expectedOrientationSign 9 5
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 9 6
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * 1))) =
      expectedOrientationSign 9 7
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 9 8
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * (1 * (-1)))) =
      expectedOrientationSign 9 9
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 9 10
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * (1 * (-1)))) =
      expectedOrientationSign 9 11
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 9 12
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * (1 * ((-1) * (-1)))) =
      expectedOrientationSign 9 13
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        ((1 : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 9 14
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]
  · change ((Equiv.Perm.sign (permutationCode 9) : ℤ) : ℚ) *
        (((-1) : ℚ) * ((-1) * ((-1) * (-1)))) =
      expectedOrientationSign 9 15
    rw [permutationSign_certificate_block9]
    norm_num [expectedPermutationSign, expectedOrientationSign]

theorem reflectionCharacterMoment_certificate_block9 :
    ∀ parity : ContractionParity, ∀ rank : Fin 17,
      encodedReflectionCharacterMoment parity 9 rank =
        expectedReflectionCharacterMoment parity 9 rank := by
  intro parity rank
  cases parity <;> fin_cases rank <;>
    norm_num [encodedReflectionCharacterMoment,
      ContractionParity.character,
      signedAxisTrace_certificate_block9,
      orientationSign_certificate_block9,
      expectedSignedAxisTrace, expectedOrientationSign,
      expectedReflectionCharacterMoment, Fin.sum_univ_succ]

end HypercubicRawFDCharacterCensus
end YangMills
end QuantumTheory
end Mettapedia
