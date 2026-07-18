import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk000
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk001
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk002
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk003
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk004
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk005
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk006
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk008
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk009
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk010
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk011
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk012
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk013
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk014
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk015
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk016
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk017
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk018
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk019
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk020
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk021
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk022
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk023
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk024
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk025
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk026
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk027
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk028
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessChunk029
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessFundamentalCertificate

/-! # Kernel-checked semantic witnesses for selected standard trace rows -/

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceWitnessCertificate

open HypercubicDimension16PhysicalTraceWitnessExecutable

theorem physicalTraceWitness_valid (index : Fin 11556) :
    EncodedPhysicalTraceWitnessValid index := by
  by_cases h000 : index.1 < 256
  · let localIndex : Fin 256 := ⟨index.1 - 0, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk000.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk000.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk000.chunk_physical_trace_witnesses_valid localIndex
  by_cases h001 : index.1 < 512
  · let localIndex : Fin 256 := ⟨index.1 - 256, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk001.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk001.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk001.chunk_physical_trace_witnesses_valid localIndex
  by_cases h002 : index.1 < 768
  · let localIndex : Fin 256 := ⟨index.1 - 512, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk002.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk002.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk002.chunk_physical_trace_witnesses_valid localIndex
  by_cases h003 : index.1 < 1024
  · let localIndex : Fin 256 := ⟨index.1 - 768, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk003.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk003.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk003.chunk_physical_trace_witnesses_valid localIndex
  by_cases h004 : index.1 < 1280
  · let localIndex : Fin 256 := ⟨index.1 - 1024, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk004.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk004.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk004.chunk_physical_trace_witnesses_valid localIndex
  by_cases h005 : index.1 < 1536
  · let localIndex : Fin 256 := ⟨index.1 - 1280, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk005.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk005.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk005.chunk_physical_trace_witnesses_valid localIndex
  by_cases h006 : index.1 < 1792
  · let localIndex : Fin 256 := ⟨index.1 - 1536, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk006.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk006.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk006.chunk_physical_trace_witnesses_valid localIndex
  by_cases h007 : index.1 < 2048
  · let localIndex : Fin 256 := ⟨index.1 - 1792, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk007.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk007.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk007.chunk_physical_trace_witnesses_valid localIndex
  by_cases h008 : index.1 < 2304
  · let localIndex : Fin 256 := ⟨index.1 - 2048, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk008.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk008.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk008.chunk_physical_trace_witnesses_valid localIndex
  by_cases h009 : index.1 < 2560
  · let localIndex : Fin 256 := ⟨index.1 - 2304, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk009.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk009.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk009.chunk_physical_trace_witnesses_valid localIndex
  by_cases h010 : index.1 < 2816
  · let localIndex : Fin 256 := ⟨index.1 - 2560, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk010.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk010.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk010.chunk_physical_trace_witnesses_valid localIndex
  by_cases h011 : index.1 < 3072
  · let localIndex : Fin 256 := ⟨index.1 - 2816, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk011.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk011.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk011.chunk_physical_trace_witnesses_valid localIndex
  by_cases h012 : index.1 < 3328
  · let localIndex : Fin 256 := ⟨index.1 - 3072, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk012.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk012.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk012.chunk_physical_trace_witnesses_valid localIndex
  by_cases h013 : index.1 < 3584
  · let localIndex : Fin 256 := ⟨index.1 - 3328, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk013.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk013.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk013.chunk_physical_trace_witnesses_valid localIndex
  by_cases h014 : index.1 < 3840
  · let localIndex : Fin 256 := ⟨index.1 - 3584, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk014.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk014.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk014.chunk_physical_trace_witnesses_valid localIndex
  by_cases h015 : index.1 < 4096
  · let localIndex : Fin 256 := ⟨index.1 - 3840, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk015.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk015.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk015.chunk_physical_trace_witnesses_valid localIndex
  by_cases h016 : index.1 < 4352
  · let localIndex : Fin 256 := ⟨index.1 - 4096, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk016.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk016.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk016.chunk_physical_trace_witnesses_valid localIndex
  by_cases h017 : index.1 < 4608
  · let localIndex : Fin 256 := ⟨index.1 - 4352, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk017.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk017.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk017.chunk_physical_trace_witnesses_valid localIndex
  by_cases h018 : index.1 < 4864
  · let localIndex : Fin 256 := ⟨index.1 - 4608, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk018.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk018.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk018.chunk_physical_trace_witnesses_valid localIndex
  by_cases h019 : index.1 < 5120
  · let localIndex : Fin 256 := ⟨index.1 - 4864, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk019.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk019.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk019.chunk_physical_trace_witnesses_valid localIndex
  by_cases h020 : index.1 < 5376
  · let localIndex : Fin 256 := ⟨index.1 - 5120, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk020.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk020.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk020.chunk_physical_trace_witnesses_valid localIndex
  by_cases h021 : index.1 < 5632
  · let localIndex : Fin 256 := ⟨index.1 - 5376, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk021.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk021.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk021.chunk_physical_trace_witnesses_valid localIndex
  by_cases h022 : index.1 < 5888
  · let localIndex : Fin 256 := ⟨index.1 - 5632, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk022.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk022.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk022.chunk_physical_trace_witnesses_valid localIndex
  by_cases h023 : index.1 < 6144
  · let localIndex : Fin 256 := ⟨index.1 - 5888, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk023.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk023.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk023.chunk_physical_trace_witnesses_valid localIndex
  by_cases h024 : index.1 < 6400
  · let localIndex : Fin 256 := ⟨index.1 - 6144, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk024.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk024.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk024.chunk_physical_trace_witnesses_valid localIndex
  by_cases h025 : index.1 < 6656
  · let localIndex : Fin 256 := ⟨index.1 - 6400, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk025.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk025.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk025.chunk_physical_trace_witnesses_valid localIndex
  by_cases h026 : index.1 < 6912
  · let localIndex : Fin 256 := ⟨index.1 - 6656, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk026.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk026.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk026.chunk_physical_trace_witnesses_valid localIndex
  by_cases h027 : index.1 < 7168
  · let localIndex : Fin 256 := ⟨index.1 - 6912, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk027.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk027.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk027.chunk_physical_trace_witnesses_valid localIndex
  by_cases h028 : index.1 < 7424
  · let localIndex : Fin 256 := ⟨index.1 - 7168, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk028.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk028.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk028.chunk_physical_trace_witnesses_valid localIndex
  by_cases h029 : index.1 < 7680
  · let localIndex : Fin 256 := ⟨index.1 - 7424, by omega⟩
    have hequal : HypercubicDimension16PhysicalTraceWitnessChunk029.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16PhysicalTraceWitnessChunk029.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16PhysicalTraceWitnessChunk029.chunk_physical_trace_witnesses_valid localIndex
  exact
    HypercubicDimension16PhysicalTraceWitnessFundamentalCertificate.fundamental_physical_trace_witness_valid
      index (by omega)

end HypercubicDimension16PhysicalTraceWitnessCertificate
end YangMills
end QuantumTheory
end Mettapedia
