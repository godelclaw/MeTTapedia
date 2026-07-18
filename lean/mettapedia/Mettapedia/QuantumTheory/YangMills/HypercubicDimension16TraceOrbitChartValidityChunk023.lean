import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartCore

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartValidityChunk023

open HypercubicDimension16TraceOrbitChartCore

def chunkIndex (index : Fin 256) : PositiveRepresentativeIndex :=
  ⟨5888 + index.1, by
    change 5888 + index.1 < 11654
    omega⟩

theorem chunk_valid :
    ∀ index : Fin 256,
      EncodedRepresentativeValid
        (positiveRepresentativeCode (chunkIndex index)) := by
  decide

end HypercubicDimension16TraceOrbitChartValidityChunk023
end YangMills
end QuantumTheory
end Mettapedia
