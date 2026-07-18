import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessExecutable

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessChunk015

open HypercubicDimension16PhysicalTraceWitnessExecutable

def chunkIndex (localIndex : Fin 256) : Fin 11556 :=
  ⟨3840 + localIndex.1, by change 3840 + localIndex.1 < 11556; omega⟩

/-- Kernel replay of this bounded physical-row witness range. -/
theorem chunk_physical_trace_witnesses_valid :
    ∀ localIndex : Fin 256,
      EncodedPhysicalTraceWitnessValid (chunkIndex localIndex) := by
  decide +kernel

end HypercubicDimension16PhysicalTraceWitnessChunk015
end YangMills
end QuantumTheory
end Mettapedia
