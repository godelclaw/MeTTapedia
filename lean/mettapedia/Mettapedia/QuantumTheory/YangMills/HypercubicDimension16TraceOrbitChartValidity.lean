import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk000
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk001
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk002
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk003
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk004
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk005
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk006
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk008
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk009
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk010
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk011
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk012
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk013
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk014
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk015
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk016
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk017
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk018
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk019
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk020
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk021
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk022
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk023
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk024
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk025
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk026
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk027
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk028
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk029
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk030
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk031
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk032
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk033
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk034
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk035
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk036
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk037
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk038
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk039
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk040
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk041
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk042
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk043
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk044
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitChartValidityChunk045

/-!
# Kernel certificate for the fixed-width positive orbit chart

Each generated data chunk is checked independently for width, coordinate
ranges, and the two trace-permutation inverse laws.  The chunk theorems are
assembled here into the global validity statement used by the decoder.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitChartValidity

open HypercubicDimension16TraceOrbitChartCore

/-- Every generated entry passes the fixed-width and permutation checks. -/
theorem positiveRepresentativeCodes_valid
    (index : PositiveRepresentativeIndex) :
    EncodedRepresentativeValid (positiveRepresentativeCode index) := by
  by_cases h000 : index.1 < 256
  · let localIndex : Fin 256 := ⟨index.1 - 0, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk000.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk000.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk000.chunk_valid localIndex
  by_cases h001 : index.1 < 512
  · let localIndex : Fin 256 := ⟨index.1 - 256, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk001.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk001.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk001.chunk_valid localIndex
  by_cases h002 : index.1 < 768
  · let localIndex : Fin 256 := ⟨index.1 - 512, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk002.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk002.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk002.chunk_valid localIndex
  by_cases h003 : index.1 < 1024
  · let localIndex : Fin 256 := ⟨index.1 - 768, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk003.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk003.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk003.chunk_valid localIndex
  by_cases h004 : index.1 < 1280
  · let localIndex : Fin 256 := ⟨index.1 - 1024, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk004.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk004.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk004.chunk_valid localIndex
  by_cases h005 : index.1 < 1536
  · let localIndex : Fin 256 := ⟨index.1 - 1280, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk005.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk005.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk005.chunk_valid localIndex
  by_cases h006 : index.1 < 1792
  · let localIndex : Fin 256 := ⟨index.1 - 1536, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk006.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk006.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk006.chunk_valid localIndex
  by_cases h007 : index.1 < 2048
  · let localIndex : Fin 256 := ⟨index.1 - 1792, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk007.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk007.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk007.chunk_valid localIndex
  by_cases h008 : index.1 < 2304
  · let localIndex : Fin 256 := ⟨index.1 - 2048, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk008.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk008.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk008.chunk_valid localIndex
  by_cases h009 : index.1 < 2560
  · let localIndex : Fin 256 := ⟨index.1 - 2304, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk009.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk009.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk009.chunk_valid localIndex
  by_cases h010 : index.1 < 2816
  · let localIndex : Fin 256 := ⟨index.1 - 2560, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk010.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk010.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk010.chunk_valid localIndex
  by_cases h011 : index.1 < 3072
  · let localIndex : Fin 256 := ⟨index.1 - 2816, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk011.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk011.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk011.chunk_valid localIndex
  by_cases h012 : index.1 < 3328
  · let localIndex : Fin 256 := ⟨index.1 - 3072, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk012.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk012.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk012.chunk_valid localIndex
  by_cases h013 : index.1 < 3584
  · let localIndex : Fin 256 := ⟨index.1 - 3328, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk013.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk013.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk013.chunk_valid localIndex
  by_cases h014 : index.1 < 3840
  · let localIndex : Fin 256 := ⟨index.1 - 3584, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk014.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk014.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk014.chunk_valid localIndex
  by_cases h015 : index.1 < 4096
  · let localIndex : Fin 256 := ⟨index.1 - 3840, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk015.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk015.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk015.chunk_valid localIndex
  by_cases h016 : index.1 < 4352
  · let localIndex : Fin 256 := ⟨index.1 - 4096, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk016.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk016.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk016.chunk_valid localIndex
  by_cases h017 : index.1 < 4608
  · let localIndex : Fin 256 := ⟨index.1 - 4352, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk017.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk017.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk017.chunk_valid localIndex
  by_cases h018 : index.1 < 4864
  · let localIndex : Fin 256 := ⟨index.1 - 4608, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk018.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk018.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk018.chunk_valid localIndex
  by_cases h019 : index.1 < 5120
  · let localIndex : Fin 256 := ⟨index.1 - 4864, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk019.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk019.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk019.chunk_valid localIndex
  by_cases h020 : index.1 < 5376
  · let localIndex : Fin 256 := ⟨index.1 - 5120, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk020.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk020.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk020.chunk_valid localIndex
  by_cases h021 : index.1 < 5632
  · let localIndex : Fin 256 := ⟨index.1 - 5376, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk021.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk021.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk021.chunk_valid localIndex
  by_cases h022 : index.1 < 5888
  · let localIndex : Fin 256 := ⟨index.1 - 5632, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk022.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk022.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk022.chunk_valid localIndex
  by_cases h023 : index.1 < 6144
  · let localIndex : Fin 256 := ⟨index.1 - 5888, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk023.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk023.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk023.chunk_valid localIndex
  by_cases h024 : index.1 < 6400
  · let localIndex : Fin 256 := ⟨index.1 - 6144, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk024.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk024.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk024.chunk_valid localIndex
  by_cases h025 : index.1 < 6656
  · let localIndex : Fin 256 := ⟨index.1 - 6400, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk025.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk025.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk025.chunk_valid localIndex
  by_cases h026 : index.1 < 6912
  · let localIndex : Fin 256 := ⟨index.1 - 6656, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk026.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk026.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk026.chunk_valid localIndex
  by_cases h027 : index.1 < 7168
  · let localIndex : Fin 256 := ⟨index.1 - 6912, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk027.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk027.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk027.chunk_valid localIndex
  by_cases h028 : index.1 < 7424
  · let localIndex : Fin 256 := ⟨index.1 - 7168, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk028.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk028.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk028.chunk_valid localIndex
  by_cases h029 : index.1 < 7680
  · let localIndex : Fin 256 := ⟨index.1 - 7424, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk029.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk029.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk029.chunk_valid localIndex
  by_cases h030 : index.1 < 7936
  · let localIndex : Fin 256 := ⟨index.1 - 7680, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk030.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk030.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk030.chunk_valid localIndex
  by_cases h031 : index.1 < 8192
  · let localIndex : Fin 256 := ⟨index.1 - 7936, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk031.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk031.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk031.chunk_valid localIndex
  by_cases h032 : index.1 < 8448
  · let localIndex : Fin 256 := ⟨index.1 - 8192, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk032.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk032.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk032.chunk_valid localIndex
  by_cases h033 : index.1 < 8704
  · let localIndex : Fin 256 := ⟨index.1 - 8448, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk033.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk033.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk033.chunk_valid localIndex
  by_cases h034 : index.1 < 8960
  · let localIndex : Fin 256 := ⟨index.1 - 8704, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk034.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk034.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk034.chunk_valid localIndex
  by_cases h035 : index.1 < 9216
  · let localIndex : Fin 256 := ⟨index.1 - 8960, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk035.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk035.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk035.chunk_valid localIndex
  by_cases h036 : index.1 < 9472
  · let localIndex : Fin 256 := ⟨index.1 - 9216, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk036.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk036.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk036.chunk_valid localIndex
  by_cases h037 : index.1 < 9728
  · let localIndex : Fin 256 := ⟨index.1 - 9472, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk037.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk037.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk037.chunk_valid localIndex
  by_cases h038 : index.1 < 9984
  · let localIndex : Fin 256 := ⟨index.1 - 9728, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk038.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk038.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk038.chunk_valid localIndex
  by_cases h039 : index.1 < 10240
  · let localIndex : Fin 256 := ⟨index.1 - 9984, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk039.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk039.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk039.chunk_valid localIndex
  by_cases h040 : index.1 < 10496
  · let localIndex : Fin 256 := ⟨index.1 - 10240, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk040.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk040.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk040.chunk_valid localIndex
  by_cases h041 : index.1 < 10752
  · let localIndex : Fin 256 := ⟨index.1 - 10496, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk041.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk041.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk041.chunk_valid localIndex
  by_cases h042 : index.1 < 11008
  · let localIndex : Fin 256 := ⟨index.1 - 10752, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk042.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk042.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk042.chunk_valid localIndex
  by_cases h043 : index.1 < 11264
  · let localIndex : Fin 256 := ⟨index.1 - 11008, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk043.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk043.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk043.chunk_valid localIndex
  by_cases h044 : index.1 < 11520
  · let localIndex : Fin 256 := ⟨index.1 - 11264, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk044.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk044.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk044.chunk_valid localIndex
  · let localIndex : Fin 134 := ⟨index.1 - 11520, by
      change index.1 - 11520 < 134
      have := index.isLt
      change index.1 < 11654 at this
      omega⟩
    have hequal : HypercubicDimension16TraceOrbitChartValidityChunk045.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitChartValidityChunk045.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitChartValidityChunk045.chunk_valid localIndex

end HypercubicDimension16TraceOrbitChartValidity
end YangMills
end QuantumTheory
end Mettapedia
