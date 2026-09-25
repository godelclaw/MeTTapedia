import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitProductSignatureTable
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceOrbitProductSignatureKernelTables
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16DecoderTableRewrite

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceOrbitProductSignatureTableChunk011

open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitProductSignatureTable

def chunkIndex (localIndex : Fin 390) : PositiveRepresentativeIndex :=
  ⟨11264 + localIndex.1, by
    change 11264 + localIndex.1 < 11654
    omega⟩

theorem chunk_rank_tables_block0 :
    ∀ j : Fin 64, ∀ hij : 0 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨0 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block1 :
    ∀ j : Fin 64, ∀ hij : 1 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨1 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block2 :
    ∀ j : Fin 64, ∀ hij : 2 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨2 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block3 :
    ∀ j : Fin 64, ∀ hij : 3 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨3 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block4 :
    ∀ j : Fin 64, ∀ hij : 4 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨4 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block5 :
    ∀ j : Fin 64, ∀ hij : 5 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨5 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block6 :
    ∀ j : Fin 64, ∀ hij : 6 * 64 + j.1 < 390,
      (fun localIndex : Fin 390 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨6 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

/-- Bounded replay of the rank inverse and sorted-signature lookup. -/
theorem chunk_rank_tables :
    ∀ localIndex : Fin 390,
      representativeAtProductSignatureRank
          (productSignatureRank (chunkIndex localIndex)) =
          chunkIndex localIndex ∧
        sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
          expectedProductSignature (chunkIndex localIndex) :=
  HypercubicDimension16DecoderTableRewrite.forall_fin_of_blocks 64 7 (by decide) _
    fun k hk => match k, hk with
      | 0, _ => chunk_rank_tables_block0
      | 1, _ => chunk_rank_tables_block1
      | 2, _ => chunk_rank_tables_block2
      | 3, _ => chunk_rank_tables_block3
      | 4, _ => chunk_rank_tables_block4
      | 5, _ => chunk_rank_tables_block5
      | 6, _ => chunk_rank_tables_block6
      | _ + 7, h => absurd h (by omega)

theorem chunk_sorted_lt_block0 :
    ∀ j : Fin 64, ∀ hij : 0 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨0 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block1 :
    ∀ j : Fin 64, ∀ hij : 1 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨1 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block2 :
    ∀ j : Fin 64, ∀ hij : 2 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨2 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block3 :
    ∀ j : Fin 64, ∀ hij : 3 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨3 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block4 :
    ∀ j : Fin 64, ∀ hij : 4 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨4 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block5 :
    ∀ j : Fin 64, ∀ hij : 5 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨5 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block6 :
    ∀ j : Fin 64, ∀ hij : 6 * 64 + j.1 < 389,
      (fun localIndex : Fin 389 =>
        sortedProductSignatureAt (11264 + localIndex.1) <
          sortedProductSignatureAt (11264 + localIndex.1 + 1)
        ) ⟨6 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

/-- Bounded replay of adjacent strict increase in the sorted table. -/
theorem chunk_sorted_lt :
    ∀ localIndex : Fin 389,
      sortedProductSignatureAt (11264 + localIndex.1) <
        sortedProductSignatureAt (11264 + localIndex.1 + 1) :=
  HypercubicDimension16DecoderTableRewrite.forall_fin_of_blocks 64 7 (by decide) _
    fun k hk => match k, hk with
      | 0, _ => chunk_sorted_lt_block0
      | 1, _ => chunk_sorted_lt_block1
      | 2, _ => chunk_sorted_lt_block2
      | 3, _ => chunk_sorted_lt_block3
      | 4, _ => chunk_sorted_lt_block4
      | 5, _ => chunk_sorted_lt_block5
      | 6, _ => chunk_sorted_lt_block6
      | _ + 7, h => absurd h (by omega)

end HypercubicDimension16TraceOrbitProductSignatureTableChunk011
end YangMills
end QuantumTheory
end Mettapedia
