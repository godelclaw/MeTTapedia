import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessExecutable
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16DecoderTableRewrite
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessKernelTables
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartKernelTables

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessFundamentalChunk032

open HypercubicDimension16PhysicalTraceWitnessExecutable

def chunkIndex (localIndex : Fin 64) : Fin 11556 :=
  ⟨9728 + localIndex.1, by change 9728 + localIndex.1 < 11556; omega⟩

theorem chunk_physical_trace_witnesses_valid_block0 :
    ∀ j : Fin 16, ∀ hij : 0 * 16 + j.1 < 64,
      (fun localIndex : Fin 64 =>
        EncodedPhysicalTraceWitnessValid (chunkIndex localIndex)
        ) ⟨0 * 16 + j.1, hij⟩ := by
  rewrite_decoders_to_tables [
    HypercubicDimension16PhysicalTraceWitnessKernelTables.decodedPhysicalTraceWitnessChunk_eq_table,
    HypercubicDimension16TraceOrbitChartKernelTables.decodedPositiveRepresentativeWordChunk_eq_table]
  decide +kernel

theorem chunk_physical_trace_witnesses_valid_block1 :
    ∀ j : Fin 16, ∀ hij : 1 * 16 + j.1 < 64,
      (fun localIndex : Fin 64 =>
        EncodedPhysicalTraceWitnessValid (chunkIndex localIndex)
        ) ⟨1 * 16 + j.1, hij⟩ := by
  rewrite_decoders_to_tables [
    HypercubicDimension16PhysicalTraceWitnessKernelTables.decodedPhysicalTraceWitnessChunk_eq_table,
    HypercubicDimension16TraceOrbitChartKernelTables.decodedPositiveRepresentativeWordChunk_eq_table]
  decide +kernel

theorem chunk_physical_trace_witnesses_valid_block2 :
    ∀ j : Fin 16, ∀ hij : 2 * 16 + j.1 < 64,
      (fun localIndex : Fin 64 =>
        EncodedPhysicalTraceWitnessValid (chunkIndex localIndex)
        ) ⟨2 * 16 + j.1, hij⟩ := by
  rewrite_decoders_to_tables [
    HypercubicDimension16PhysicalTraceWitnessKernelTables.decodedPhysicalTraceWitnessChunk_eq_table,
    HypercubicDimension16TraceOrbitChartKernelTables.decodedPositiveRepresentativeWordChunk_eq_table]
  decide +kernel

theorem chunk_physical_trace_witnesses_valid_block3 :
    ∀ j : Fin 16, ∀ hij : 3 * 16 + j.1 < 64,
      (fun localIndex : Fin 64 =>
        EncodedPhysicalTraceWitnessValid (chunkIndex localIndex)
        ) ⟨3 * 16 + j.1, hij⟩ := by
  rewrite_decoders_to_tables [
    HypercubicDimension16PhysicalTraceWitnessKernelTables.decodedPhysicalTraceWitnessChunk_eq_table,
    HypercubicDimension16TraceOrbitChartKernelTables.decodedPositiveRepresentativeWordChunk_eq_table]
  decide +kernel

/-- Kernel replay of this bounded six-term standard-trace witness range. -/
theorem chunk_physical_trace_witnesses_valid :
    ∀ localIndex : Fin 64,
      EncodedPhysicalTraceWitnessValid (chunkIndex localIndex) :=
  HypercubicDimension16DecoderTableRewrite.forall_fin_of_blocks 16 4 (by decide) _
    fun k hk => match k, hk with
      | 0, _ => chunk_physical_trace_witnesses_valid_block0
      | 1, _ => chunk_physical_trace_witnesses_valid_block1
      | 2, _ => chunk_physical_trace_witnesses_valid_block2
      | 3, _ => chunk_physical_trace_witnesses_valid_block3
      | _ + 4, h => absurd h (by omega)

end HypercubicDimension16PhysicalTraceWitnessFundamentalChunk032
end YangMills
end QuantumTheory
end Mettapedia
