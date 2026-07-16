import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-! Kernel-checked class-compressed sector block 1. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16CompressionCensus

theorem classCompressedSectorCharacter_certificate_block1
    (fieldIndex : Fin 8) :
    classCompressedSectorCharacter 1 (fieldIndex.1 + 1) =
      expectedClassCompressedSectorCharacter 1
        (fieldIndex.1 + 1) := by
  fin_cases fieldIndex <;>
    norm_num (config := { maxSteps := 1000000 })
      [classCompressedSectorCharacter,
      classPartitionDerivativeCharacter, classCycleLetterCharacter,
      classPowerTrace, classPowerTraceInt, powerTraceRows, fieldPartitions,
      derivativeCountForFields, expectedClassCompressedSectorCharacter,
      Finset.sum_range_succ]

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
