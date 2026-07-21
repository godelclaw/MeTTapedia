import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-! Kernel-checked compression replay block 6. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionCensus

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus

theorem decodedPowerTraceReplayCheckAt_certificate_block6 :
    decodedPowerTraceReplayCheckAt 6 = true := by
  norm_num [decodedPowerTraceReplayCheckAt, allFin16,
    recurrentVectorPowerTrace, recurrentVectorPowerTraceTerm,
    powerAxis, powerReflected, powerTraceClassOf, powerTraceClassFrom,
    classPowerTraceInt, powerTraceRows,
    decodedHypercubicCharacterElement, characterReflectionCode,
    characterReflectionEntry, permutationCode,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem decodedOrientationReplayCheckAt_certificate_block6 :
    decodedOrientationReplayCheckAt 6 = true := by
  unfold decodedOrientationReplayCheckAt allFin16
  simp_rw [orientationSign_certificate]
  norm_num [powerTraceClassOf, powerTraceClassFrom,
    recurrentVectorPowerTrace, recurrentVectorPowerTraceTerm,
    powerAxis, powerReflected, classOrientationSign,
    expectedOrientationSign, decodedHypercubicCharacterElement,
    characterReflectionCode, characterReflectionEntry, permutationCode,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]

theorem decodedPowerTraceClassAt_certificate_block6
    (reflectionMask : Fin 16) :
    decodedPowerTraceClassAt 6 reflectionMask =
      expectedPowerTraceClassAt 6 reflectionMask := by
  fin_cases reflectionMask <;>
    norm_num [decodedPowerTraceClassAt, expectedPowerTraceClassAt,
      expectedPowerTraceClassRows, powerTraceClassOf, powerTraceClassFrom,
      recurrentVectorPowerTrace, recurrentVectorPowerTraceTerm,
      powerAxis, powerReflected, decodedHypercubicCharacterElement,
      characterReflectionCode, characterReflectionEntry, permutationCode,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three]
  all_goals simp_all

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
