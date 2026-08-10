import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-! Kernel-checked compression replay block 2. -/

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

theorem decodedPowerTraceReplayCheckAt_certificate_block2 :
    decodedPowerTraceReplayCheckAt 2 = true := by
  decide +kernel

theorem decodedOrientationReplayCheckAt_certificate_block2 :
    decodedOrientationReplayCheckAt 2 = true := by
  decide +kernel

theorem decodedPowerTraceClassAt_certificate_block2
    (reflectionMask : Fin 16) :
    decodedPowerTraceClassAt 2 reflectionMask =
      expectedPowerTraceClassAt 2 reflectionMask := by
  decide +kernel +revert

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
