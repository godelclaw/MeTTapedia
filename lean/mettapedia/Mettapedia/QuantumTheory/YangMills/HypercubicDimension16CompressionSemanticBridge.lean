import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionReplayCertificate
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionSectorCertificate

/-!
# Semantic bridge for the dimension-sixteen compression census

The finite class tables are connected here to the literal signed-permutation
elements used as arguments of the cycle-index expression.  The bridge first
extracts pointwise facts from the exhaustive Boolean replay and then lifts the
power-trace equality through the cycle-index recursion.  It does not realize
that expression as the character of a finite normal-form carrier.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus

theorem allFin16_apply_true {predicate : Fin 16 → Bool}
    (certificate : allFin16 predicate = true) (index : Fin 16) :
    predicate index = true := by
  fin_cases index <;> simp_all [allFin16]

theorem decodedPowerTraceInt_certificate
    (permutation : Fin 24) (reflectionMask exponentIndex : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    recurrentVectorPowerTrace h (exponentIndex.1 + 1) =
      classPowerTraceInt (powerTraceClassOf h) (exponentIndex.1 + 1) := by
  have replay := decodedPowerTraceReplayCheckAt_certificate permutation
  unfold decodedPowerTraceReplayCheckAt at replay
  have reflectionReplay := allFin16_apply_true replay reflectionMask
  dsimp only at reflectionReplay
  have exponentReplay := allFin16_apply_true reflectionReplay exponentIndex
  exact of_decide_eq_true exponentReplay

theorem decodedOrientationSign_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    Hypercubic4.orientationSign h =
      classOrientationSign (powerTraceClassOf h) := by
  have replay := decodedOrientationReplayCheckAt_certificate permutation
  unfold decodedOrientationReplayCheckAt at replay
  have reflectionReplay := allFin16_apply_true replay reflectionMask
  exact of_decide_eq_true reflectionReplay

theorem decodedVectorCharacter_pow_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16)
    (exponent : ℕ) (exponentPositive : 1 ≤ exponent)
    (exponentBound : exponent ≤ 16) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    vectorCharacter (h ^ exponent) =
      classPowerTrace (powerTraceClassOf h) exponent := by
  let exponentIndex : Fin 16 :=
    ⟨exponent - 1, by omega⟩
  have replay := decodedPowerTraceInt_certificate
    permutation reflectionMask exponentIndex
  have exponentIndexValue : exponentIndex.1 + 1 = exponent := by
    dsimp [exponentIndex]
    omega
  let h := decodedHypercubicCharacterElement permutation reflectionMask
  calc
    vectorCharacter (h ^ exponent) =
        (recurrentVectorPowerTrace h exponent : ℚ) :=
      (recurrentVectorPowerTrace_semantic h exponent).symm
    _ = (classPowerTraceInt (powerTraceClassOf h) exponent : ℚ) := by
      exact_mod_cast (by simpa [h, exponentIndexValue] using replay)
    _ = classPowerTrace (powerTraceClassOf h) exponent := rfl

theorem decodedCycleLetterCharacter_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16)
    (cycleLength localDerivativeCount : ℕ)
    (cyclePositive : 1 ≤ cycleLength) (cycleBound : cycleLength ≤ 8) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    cycleLetterCharacter h cycleLength localDerivativeCount =
      classCycleLetterCharacter (powerTraceClassOf h)
        cycleLength localDerivativeCount := by
  let h := decodedHypercubicCharacterElement permutation reflectionMask
  have firstTrace := decodedVectorCharacter_pow_certificate
    permutation reflectionMask cycleLength cyclePositive (by omega)
  have secondTrace := decodedVectorCharacter_pow_certificate
    permutation reflectionMask (2 * cycleLength) (by omega) (by omega)
  have powerIdentity : (h ^ cycleLength) ^ 2 = h ^ (2 * cycleLength) := by
    rw [← pow_mul]
    congr 1
    omega
  unfold cycleLetterCharacter classCycleLetterCharacter twoFormCharacter
  dsimp only
  rw [firstTrace, powerIdentity, secondTrace]

theorem decodedPartitionDerivativeCharacter_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16)
    (parts : List ℕ) (remainingDegree : ℕ)
    (partsBound : ∀ cycleLength ∈ parts,
      1 ≤ cycleLength ∧ cycleLength ≤ 8) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    partitionDerivativeCharacter h parts remainingDegree =
      classPartitionDerivativeCharacter (powerTraceClassOf h)
        parts remainingDegree := by
  let h := decodedHypercubicCharacterElement permutation reflectionMask
  induction parts generalizing remainingDegree with
  | nil => simp [partitionDerivativeCharacter,
      classPartitionDerivativeCharacter]
  | cons cycleLength rest inductionHypothesis =>
      simp only [partitionDerivativeCharacter,
        classPartitionDerivativeCharacter]
      apply Finset.sum_congr rfl
      intro localDerivativeCount _
      rw [decodedCycleLetterCharacter_certificate permutation reflectionMask
        cycleLength localDerivativeCount
        (partsBound cycleLength (by simp)).1
        (partsBound cycleLength (by simp)).2]
      rw [inductionHypothesis]
      intro restCycle restMembership
      exact partsBound restCycle (by simp [restMembership])

theorem fieldPartitions_entry_bounds (fieldIndex : Fin 8)
    (parts : List ℕ)
    (membership : parts ∈ fieldPartitions (fieldIndex.1 + 1)) :
    ∀ cycleLength ∈ parts, 1 ≤ cycleLength ∧ cycleLength ≤ 8 := by
  fin_cases fieldIndex <;> simp [fieldPartitions] at membership <;> aesop

theorem decodedCompressedSectorCharacter_certificate
    (permutation : Fin 24) (reflectionMask : Fin 16)
    (fieldIndex : Fin 8) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    compressedSectorCharacter h (fieldIndex.1 + 1) =
      classCompressedSectorCharacter (powerTraceClassOf h)
        (fieldIndex.1 + 1) := by
  let h := decodedHypercubicCharacterElement permutation reflectionMask
  unfold compressedSectorCharacter classCompressedSectorCharacter
  apply Finset.sum_congr rfl
  intro parts membership
  apply decodedPartitionDerivativeCharacter_certificate
  exact fieldPartitions_entry_bounds fieldIndex parts (by simpa using membership)

def classParityCharacter (parity : ContractionParity)
    (traceClass : PowerTraceClass) : ℚ :=
  match parity with
  | .scalar => 1
  | .pseudoscalar => classOrientationSign traceClass

theorem decodedCompressionSummand_certificate
    (parity : ContractionParity) (permutation : Fin 24)
    (reflectionMask : Fin 16) (fieldIndex : Fin 8) :
    let h := decodedHypercubicCharacterElement permutation reflectionMask
    parity.character h *
        compressedSectorCharacter h (fieldIndex.1 + 1) =
      classParityCharacter parity
          (expectedPowerTraceClassAt permutation reflectionMask) *
        classCompressedSectorCharacter
          (expectedPowerTraceClassAt permutation reflectionMask)
          (fieldIndex.1 + 1) := by
  let h := decodedHypercubicCharacterElement permutation reflectionMask
  cases parity
  · simp only [ContractionParity.character, classParityCharacter, one_mul]
    rw [decodedCompressedSectorCharacter_certificate]
    change classCompressedSectorCharacter
        (decodedPowerTraceClassAt permutation reflectionMask)
          (fieldIndex.1 + 1) = _
    rw [decodedPowerTraceClassAt_certificate]
  · simp only [ContractionParity.character, classParityCharacter]
    rw [decodedOrientationSign_certificate,
      decodedCompressedSectorCharacter_certificate]
    change classOrientationSign
          (decodedPowerTraceClassAt permutation reflectionMask) *
        classCompressedSectorCharacter
          (decodedPowerTraceClassAt permutation reflectionMask)
            (fieldIndex.1 + 1) = _
    rw [decodedPowerTraceClassAt_certificate]

theorem compressedInvariantMultiplicity_eq_classCompressed
    (parity : ContractionParity) (fieldIndex : Fin 8) :
    compressedInvariantMultiplicity parity (fieldIndex.1 + 1) =
      classCompressedInvariantMultiplicity parity
        (fieldIndex.1 + 1) := by
  unfold compressedInvariantMultiplicity encodedCompressionMoment
  unfold encodedCompressionReflectionMoment
  simp_rw [decodedCompressionSummand_certificate]
  unfold classCompressedInvariantMultiplicity
  simp_rw [classCompressedSectorCharacter_certificate]
  cases parity <;> fin_cases fieldIndex <;>
    norm_num [classParityCharacter, expectedPowerTraceClassAt,
      expectedPowerTraceClassRows, expectedClassCompressedSectorCharacter,
      classMultiplicity, classOrientationSign, Fin.sum_univ_succ]

theorem compressedInvariantMultiplicity_certificate
    (parity : ContractionParity) (fieldIndex : Fin 8) :
    compressedInvariantMultiplicity parity (fieldIndex.1 + 1) =
      expectedCompressedInvariantMultiplicity parity
        (fieldIndex.1 + 1) := by
  rw [compressedInvariantMultiplicity_eq_classCompressed]
  exact classCompressedInvariantMultiplicity_certificate parity fieldIndex

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
