import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CompressionCensus

/-! Kernel-checked compression replay block 3. -/

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

theorem decodedPowerTraceReplayCheckAt_certificate_block3 :
    decodedPowerTraceReplayCheckAt 3 = true := by
  decide +kernel

theorem decodedOrientationReplayCheckAt_certificate_block3 :
    decodedOrientationReplayCheckAt 3 = true := by
  decide +kernel

theorem decodedPowerTraceClassAt_certificate_block3
    (reflectionMask : Fin 16) :
    decodedPowerTraceClassAt 3 reflectionMask =
      expectedPowerTraceClassAt 3 reflectionMask := by
  decide +kernel +revert

end HypercubicDimension16CompressionCensus
end YangMills
end QuantumTheory
end Mettapedia
