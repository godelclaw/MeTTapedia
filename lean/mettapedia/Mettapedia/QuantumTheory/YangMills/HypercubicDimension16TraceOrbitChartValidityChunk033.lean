import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartCore
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartKernelTables

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartValidityChunk033

open HypercubicDimension16TraceOrbitChartCore

def chunkIndex (index : Fin 256) : PositiveRepresentativeIndex :=
  ⟨8448 + index.1, by
    change 8448 + index.1 < 11654
    omega⟩

theorem chunk_valid :
    ∀ index : Fin 256,
      EncodedRepresentativeValid
        (positiveRepresentativeCode (chunkIndex index)) := by
  simp only [positiveRepresentativeCode,
    HypercubicDimension16TraceOrbitChartData.positiveRepresentativeCode?,
    HypercubicDimension16TraceOrbitChartKernelTables.decodedPositiveRepresentativeWordChunk_eq_table]
  decide +kernel

end HypercubicDimension16TraceOrbitChartValidityChunk033
end YangMills
end QuantumTheory
end Mettapedia
