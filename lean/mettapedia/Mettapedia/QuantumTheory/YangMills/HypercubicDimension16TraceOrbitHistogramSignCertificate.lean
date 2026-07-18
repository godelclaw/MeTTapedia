import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk000
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk001
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk002
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk003
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk004
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk005
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk006
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk007
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk008
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk009
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk010
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk011
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk012
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk013
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk014
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk015
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk016
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk017
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk018
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk019
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk020
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk021
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk022
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk023
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk024
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk025
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk026
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk027
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk028
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk029
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk030
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk031
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk032
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk033
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk034
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk035
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk036
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk037
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk038
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk039
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk040
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk041
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk042
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk043
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk044
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitHistogramSignChunk045

/-! # Kernel-checked plane-histogram stabilizer signs -/

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitHistogramSignCertificate

open HypercubicRawFDCharacterCensus
open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitExecutableSignature
open HypercubicDimension16TraceOrbitHistogramExecutable

theorem representative_reflection_signs_positive
    (index : PositiveRepresentativeIndex) :
    ∀ reflection : Fin 16,
      directRepresentativeTensorSign index
          (decodedHypercubicCharacterElement 0 reflection) = 1 := by
  by_cases h000 : index.1 < 256
  · let localIndex : Fin 256 := ⟨index.1 - 0, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk000.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk000.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk000.chunk_reflection_signs_positive localIndex
  by_cases h001 : index.1 < 512
  · let localIndex : Fin 256 := ⟨index.1 - 256, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk001.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk001.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk001.chunk_reflection_signs_positive localIndex
  by_cases h002 : index.1 < 768
  · let localIndex : Fin 256 := ⟨index.1 - 512, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk002.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk002.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk002.chunk_reflection_signs_positive localIndex
  by_cases h003 : index.1 < 1024
  · let localIndex : Fin 256 := ⟨index.1 - 768, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk003.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk003.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk003.chunk_reflection_signs_positive localIndex
  by_cases h004 : index.1 < 1280
  · let localIndex : Fin 256 := ⟨index.1 - 1024, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk004.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk004.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk004.chunk_reflection_signs_positive localIndex
  by_cases h005 : index.1 < 1536
  · let localIndex : Fin 256 := ⟨index.1 - 1280, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk005.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk005.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk005.chunk_reflection_signs_positive localIndex
  by_cases h006 : index.1 < 1792
  · let localIndex : Fin 256 := ⟨index.1 - 1536, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk006.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk006.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk006.chunk_reflection_signs_positive localIndex
  by_cases h007 : index.1 < 2048
  · let localIndex : Fin 256 := ⟨index.1 - 1792, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk007.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk007.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk007.chunk_reflection_signs_positive localIndex
  by_cases h008 : index.1 < 2304
  · let localIndex : Fin 256 := ⟨index.1 - 2048, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk008.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk008.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk008.chunk_reflection_signs_positive localIndex
  by_cases h009 : index.1 < 2560
  · let localIndex : Fin 256 := ⟨index.1 - 2304, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk009.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk009.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk009.chunk_reflection_signs_positive localIndex
  by_cases h010 : index.1 < 2816
  · let localIndex : Fin 256 := ⟨index.1 - 2560, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk010.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk010.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk010.chunk_reflection_signs_positive localIndex
  by_cases h011 : index.1 < 3072
  · let localIndex : Fin 256 := ⟨index.1 - 2816, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk011.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk011.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk011.chunk_reflection_signs_positive localIndex
  by_cases h012 : index.1 < 3328
  · let localIndex : Fin 256 := ⟨index.1 - 3072, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk012.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk012.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk012.chunk_reflection_signs_positive localIndex
  by_cases h013 : index.1 < 3584
  · let localIndex : Fin 256 := ⟨index.1 - 3328, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk013.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk013.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk013.chunk_reflection_signs_positive localIndex
  by_cases h014 : index.1 < 3840
  · let localIndex : Fin 256 := ⟨index.1 - 3584, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk014.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk014.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk014.chunk_reflection_signs_positive localIndex
  by_cases h015 : index.1 < 4096
  · let localIndex : Fin 256 := ⟨index.1 - 3840, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk015.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk015.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk015.chunk_reflection_signs_positive localIndex
  by_cases h016 : index.1 < 4352
  · let localIndex : Fin 256 := ⟨index.1 - 4096, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk016.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk016.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk016.chunk_reflection_signs_positive localIndex
  by_cases h017 : index.1 < 4608
  · let localIndex : Fin 256 := ⟨index.1 - 4352, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk017.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk017.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk017.chunk_reflection_signs_positive localIndex
  by_cases h018 : index.1 < 4864
  · let localIndex : Fin 256 := ⟨index.1 - 4608, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk018.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk018.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk018.chunk_reflection_signs_positive localIndex
  by_cases h019 : index.1 < 5120
  · let localIndex : Fin 256 := ⟨index.1 - 4864, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk019.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk019.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk019.chunk_reflection_signs_positive localIndex
  by_cases h020 : index.1 < 5376
  · let localIndex : Fin 256 := ⟨index.1 - 5120, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk020.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk020.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk020.chunk_reflection_signs_positive localIndex
  by_cases h021 : index.1 < 5632
  · let localIndex : Fin 256 := ⟨index.1 - 5376, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk021.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk021.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk021.chunk_reflection_signs_positive localIndex
  by_cases h022 : index.1 < 5888
  · let localIndex : Fin 256 := ⟨index.1 - 5632, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk022.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk022.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk022.chunk_reflection_signs_positive localIndex
  by_cases h023 : index.1 < 6144
  · let localIndex : Fin 256 := ⟨index.1 - 5888, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk023.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk023.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk023.chunk_reflection_signs_positive localIndex
  by_cases h024 : index.1 < 6400
  · let localIndex : Fin 256 := ⟨index.1 - 6144, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk024.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk024.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk024.chunk_reflection_signs_positive localIndex
  by_cases h025 : index.1 < 6656
  · let localIndex : Fin 256 := ⟨index.1 - 6400, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk025.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk025.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk025.chunk_reflection_signs_positive localIndex
  by_cases h026 : index.1 < 6912
  · let localIndex : Fin 256 := ⟨index.1 - 6656, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk026.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk026.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk026.chunk_reflection_signs_positive localIndex
  by_cases h027 : index.1 < 7168
  · let localIndex : Fin 256 := ⟨index.1 - 6912, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk027.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk027.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk027.chunk_reflection_signs_positive localIndex
  by_cases h028 : index.1 < 7424
  · let localIndex : Fin 256 := ⟨index.1 - 7168, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk028.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk028.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk028.chunk_reflection_signs_positive localIndex
  by_cases h029 : index.1 < 7680
  · let localIndex : Fin 256 := ⟨index.1 - 7424, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk029.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk029.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk029.chunk_reflection_signs_positive localIndex
  by_cases h030 : index.1 < 7936
  · let localIndex : Fin 256 := ⟨index.1 - 7680, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk030.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk030.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk030.chunk_reflection_signs_positive localIndex
  by_cases h031 : index.1 < 8192
  · let localIndex : Fin 256 := ⟨index.1 - 7936, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk031.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk031.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk031.chunk_reflection_signs_positive localIndex
  by_cases h032 : index.1 < 8448
  · let localIndex : Fin 256 := ⟨index.1 - 8192, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk032.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk032.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk032.chunk_reflection_signs_positive localIndex
  by_cases h033 : index.1 < 8704
  · let localIndex : Fin 256 := ⟨index.1 - 8448, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk033.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk033.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk033.chunk_reflection_signs_positive localIndex
  by_cases h034 : index.1 < 8960
  · let localIndex : Fin 256 := ⟨index.1 - 8704, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk034.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk034.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk034.chunk_reflection_signs_positive localIndex
  by_cases h035 : index.1 < 9216
  · let localIndex : Fin 256 := ⟨index.1 - 8960, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk035.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk035.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk035.chunk_reflection_signs_positive localIndex
  by_cases h036 : index.1 < 9472
  · let localIndex : Fin 256 := ⟨index.1 - 9216, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk036.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk036.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk036.chunk_reflection_signs_positive localIndex
  by_cases h037 : index.1 < 9728
  · let localIndex : Fin 256 := ⟨index.1 - 9472, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk037.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk037.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk037.chunk_reflection_signs_positive localIndex
  by_cases h038 : index.1 < 9984
  · let localIndex : Fin 256 := ⟨index.1 - 9728, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk038.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk038.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk038.chunk_reflection_signs_positive localIndex
  by_cases h039 : index.1 < 10240
  · let localIndex : Fin 256 := ⟨index.1 - 9984, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk039.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk039.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk039.chunk_reflection_signs_positive localIndex
  by_cases h040 : index.1 < 10496
  · let localIndex : Fin 256 := ⟨index.1 - 10240, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk040.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk040.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk040.chunk_reflection_signs_positive localIndex
  by_cases h041 : index.1 < 10752
  · let localIndex : Fin 256 := ⟨index.1 - 10496, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk041.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk041.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk041.chunk_reflection_signs_positive localIndex
  by_cases h042 : index.1 < 11008
  · let localIndex : Fin 256 := ⟨index.1 - 10752, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk042.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk042.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk042.chunk_reflection_signs_positive localIndex
  by_cases h043 : index.1 < 11264
  · let localIndex : Fin 256 := ⟨index.1 - 11008, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk043.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk043.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk043.chunk_reflection_signs_positive localIndex
  by_cases h044 : index.1 < 11520
  · let localIndex : Fin 256 := ⟨index.1 - 11264, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk044.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk044.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk044.chunk_reflection_signs_positive localIndex
  have hindex : index.1 < 11654 := by
    simpa [PositiveRepresentativeIndex,
      HypercubicDimension16TraceOrbitChartData.positiveRepresentativeCount]
      using index.isLt
  let localIndex : Fin 134 := ⟨index.1 - 11520, by omega⟩
  have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk045.chunkIndex localIndex = index := by
    apply Fin.ext
    simp [HypercubicDimension16TraceOrbitHistogramSignChunk045.chunkIndex, localIndex] <;> omega
  rw [← hequal]
  exact HypercubicDimension16TraceOrbitHistogramSignChunk045.chunk_reflection_signs_positive localIndex

theorem representative_unsigned_histogram_stabilizers_positive
    (index : PositiveRepresentativeIndex) :
    ∀ permutation : Fin 24,
      directRepresentativePlaneHistogramAt index
          (decodedHypercubicCharacterElement permutation 0) =
        directRepresentativePlaneHistogramAt index 1 →
      directRepresentativeTensorSign index
          (decodedHypercubicCharacterElement permutation 0) = 1 := by
  by_cases h000 : index.1 < 256
  · let localIndex : Fin 256 := ⟨index.1 - 0, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk000.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk000.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk000.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h001 : index.1 < 512
  · let localIndex : Fin 256 := ⟨index.1 - 256, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk001.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk001.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk001.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h002 : index.1 < 768
  · let localIndex : Fin 256 := ⟨index.1 - 512, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk002.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk002.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk002.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h003 : index.1 < 1024
  · let localIndex : Fin 256 := ⟨index.1 - 768, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk003.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk003.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk003.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h004 : index.1 < 1280
  · let localIndex : Fin 256 := ⟨index.1 - 1024, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk004.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk004.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk004.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h005 : index.1 < 1536
  · let localIndex : Fin 256 := ⟨index.1 - 1280, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk005.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk005.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk005.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h006 : index.1 < 1792
  · let localIndex : Fin 256 := ⟨index.1 - 1536, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk006.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk006.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk006.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h007 : index.1 < 2048
  · let localIndex : Fin 256 := ⟨index.1 - 1792, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk007.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk007.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk007.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h008 : index.1 < 2304
  · let localIndex : Fin 256 := ⟨index.1 - 2048, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk008.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk008.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk008.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h009 : index.1 < 2560
  · let localIndex : Fin 256 := ⟨index.1 - 2304, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk009.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk009.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk009.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h010 : index.1 < 2816
  · let localIndex : Fin 256 := ⟨index.1 - 2560, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk010.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk010.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk010.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h011 : index.1 < 3072
  · let localIndex : Fin 256 := ⟨index.1 - 2816, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk011.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk011.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk011.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h012 : index.1 < 3328
  · let localIndex : Fin 256 := ⟨index.1 - 3072, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk012.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk012.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk012.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h013 : index.1 < 3584
  · let localIndex : Fin 256 := ⟨index.1 - 3328, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk013.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk013.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk013.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h014 : index.1 < 3840
  · let localIndex : Fin 256 := ⟨index.1 - 3584, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk014.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk014.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk014.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h015 : index.1 < 4096
  · let localIndex : Fin 256 := ⟨index.1 - 3840, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk015.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk015.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk015.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h016 : index.1 < 4352
  · let localIndex : Fin 256 := ⟨index.1 - 4096, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk016.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk016.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk016.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h017 : index.1 < 4608
  · let localIndex : Fin 256 := ⟨index.1 - 4352, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk017.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk017.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk017.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h018 : index.1 < 4864
  · let localIndex : Fin 256 := ⟨index.1 - 4608, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk018.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk018.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk018.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h019 : index.1 < 5120
  · let localIndex : Fin 256 := ⟨index.1 - 4864, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk019.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk019.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk019.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h020 : index.1 < 5376
  · let localIndex : Fin 256 := ⟨index.1 - 5120, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk020.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk020.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk020.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h021 : index.1 < 5632
  · let localIndex : Fin 256 := ⟨index.1 - 5376, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk021.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk021.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk021.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h022 : index.1 < 5888
  · let localIndex : Fin 256 := ⟨index.1 - 5632, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk022.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk022.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk022.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h023 : index.1 < 6144
  · let localIndex : Fin 256 := ⟨index.1 - 5888, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk023.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk023.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk023.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h024 : index.1 < 6400
  · let localIndex : Fin 256 := ⟨index.1 - 6144, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk024.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk024.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk024.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h025 : index.1 < 6656
  · let localIndex : Fin 256 := ⟨index.1 - 6400, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk025.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk025.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk025.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h026 : index.1 < 6912
  · let localIndex : Fin 256 := ⟨index.1 - 6656, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk026.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk026.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk026.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h027 : index.1 < 7168
  · let localIndex : Fin 256 := ⟨index.1 - 6912, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk027.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk027.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk027.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h028 : index.1 < 7424
  · let localIndex : Fin 256 := ⟨index.1 - 7168, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk028.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk028.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk028.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h029 : index.1 < 7680
  · let localIndex : Fin 256 := ⟨index.1 - 7424, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk029.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk029.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk029.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h030 : index.1 < 7936
  · let localIndex : Fin 256 := ⟨index.1 - 7680, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk030.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk030.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk030.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h031 : index.1 < 8192
  · let localIndex : Fin 256 := ⟨index.1 - 7936, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk031.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk031.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk031.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h032 : index.1 < 8448
  · let localIndex : Fin 256 := ⟨index.1 - 8192, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk032.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk032.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk032.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h033 : index.1 < 8704
  · let localIndex : Fin 256 := ⟨index.1 - 8448, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk033.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk033.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk033.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h034 : index.1 < 8960
  · let localIndex : Fin 256 := ⟨index.1 - 8704, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk034.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk034.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk034.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h035 : index.1 < 9216
  · let localIndex : Fin 256 := ⟨index.1 - 8960, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk035.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk035.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk035.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h036 : index.1 < 9472
  · let localIndex : Fin 256 := ⟨index.1 - 9216, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk036.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk036.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk036.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h037 : index.1 < 9728
  · let localIndex : Fin 256 := ⟨index.1 - 9472, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk037.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk037.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk037.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h038 : index.1 < 9984
  · let localIndex : Fin 256 := ⟨index.1 - 9728, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk038.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk038.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk038.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h039 : index.1 < 10240
  · let localIndex : Fin 256 := ⟨index.1 - 9984, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk039.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk039.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk039.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h040 : index.1 < 10496
  · let localIndex : Fin 256 := ⟨index.1 - 10240, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk040.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk040.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk040.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h041 : index.1 < 10752
  · let localIndex : Fin 256 := ⟨index.1 - 10496, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk041.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk041.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk041.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h042 : index.1 < 11008
  · let localIndex : Fin 256 := ⟨index.1 - 10752, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk042.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk042.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk042.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h043 : index.1 < 11264
  · let localIndex : Fin 256 := ⟨index.1 - 11008, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk043.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk043.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk043.chunk_unsigned_histogram_stabilizers_positive localIndex
  by_cases h044 : index.1 < 11520
  · let localIndex : Fin 256 := ⟨index.1 - 11264, by omega⟩
    have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk044.chunkIndex localIndex = index := by
      apply Fin.ext
      simp [HypercubicDimension16TraceOrbitHistogramSignChunk044.chunkIndex, localIndex] <;> omega
    rw [← hequal]
    exact HypercubicDimension16TraceOrbitHistogramSignChunk044.chunk_unsigned_histogram_stabilizers_positive localIndex
  have hindex : index.1 < 11654 := by
    simpa [PositiveRepresentativeIndex,
      HypercubicDimension16TraceOrbitChartData.positiveRepresentativeCount]
      using index.isLt
  let localIndex : Fin 134 := ⟨index.1 - 11520, by omega⟩
  have hequal : HypercubicDimension16TraceOrbitHistogramSignChunk045.chunkIndex localIndex = index := by
    apply Fin.ext
    simp [HypercubicDimension16TraceOrbitHistogramSignChunk045.chunkIndex, localIndex] <;> omega
  rw [← hequal]
  exact HypercubicDimension16TraceOrbitHistogramSignChunk045.chunk_unsigned_histogram_stabilizers_positive localIndex

/-- The two smaller replays imply the full signed stabilizer test. -/
theorem representative_histogram_stabilizers_positive
    (index : PositiveRepresentativeIndex) (code : Fin 24 × Fin 16)
    (hhistogram :
      directRepresentativePlaneHistogramAt index
          (decodedHypercubicCharacterElement code.1 code.2) =
        directRepresentativePlaneHistogramAt index 1) :
    directRepresentativeTensorSign index
        (decodedHypercubicCharacterElement code.1 code.2) = 1 := by
  have hunsignedHistogram :
      directRepresentativePlaneHistogramAt index
          (decodedHypercubicCharacterElement code.1 0) =
        directRepresentativePlaneHistogramAt index 1 := by
    rw [← directRepresentativePlaneHistogramAt_reflection_blind
      index code.1 code.2]
    exact hhistogram
  rw [directRepresentativeTensorSign_character_split,
    representative_reflection_signs_positive index code.2, mul_one]
  exact representative_unsigned_histogram_stabilizers_positive
    index code.1 hunsignedHistogram

end HypercubicDimension16TraceOrbitHistogramSignCertificate
end YangMills
end QuantumTheory
end Mettapedia
