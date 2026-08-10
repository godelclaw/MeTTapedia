import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-! Kernel-checked compression replay block 18. -/

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

theorem decodedPowerTraceReplayCheckAt_certificate_block18 :
    decodedPowerTraceReplayCheckAt 18 = true := by
  decide +kernel

theorem decodedOrientationReplayCheckAt_certificate_block18 :
    decodedOrientationReplayCheckAt 18 = true := by
  decide +kernel

theorem decodedPowerTraceClassAt_certificate_block18
    (reflectionMask : Fin 16) :
    decodedPowerTraceClassAt 18 reflectionMask =
      expectedPowerTraceClassAt 18 reflectionMask := by
  decide +kernel +revert

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
