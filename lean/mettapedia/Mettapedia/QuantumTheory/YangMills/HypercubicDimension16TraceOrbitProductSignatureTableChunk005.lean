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
namespace HypercubicDimension16TraceOrbitProductSignatureTableChunk005

open HypercubicDimension16TraceOrbitChartCore
open HypercubicDimension16TraceOrbitProductSignatureTable

def chunkIndex (localIndex : Fin 1024) : PositiveRepresentativeIndex :=
  ⟨5120 + localIndex.1, by
    change 5120 + localIndex.1 < 11654
    omega⟩

theorem chunk_rank_tables_block0 :
    ∀ j : Fin 64, ∀ hij : 0 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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
    ∀ j : Fin 64, ∀ hij : 1 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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
    ∀ j : Fin 64, ∀ hij : 2 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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
    ∀ j : Fin 64, ∀ hij : 3 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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
    ∀ j : Fin 64, ∀ hij : 4 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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
    ∀ j : Fin 64, ∀ hij : 5 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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
    ∀ j : Fin 64, ∀ hij : 6 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
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

theorem chunk_rank_tables_block7 :
    ∀ j : Fin 64, ∀ hij : 7 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨7 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block8 :
    ∀ j : Fin 64, ∀ hij : 8 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨8 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block9 :
    ∀ j : Fin 64, ∀ hij : 9 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨9 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block10 :
    ∀ j : Fin 64, ∀ hij : 10 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨10 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block11 :
    ∀ j : Fin 64, ∀ hij : 11 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨11 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block12 :
    ∀ j : Fin 64, ∀ hij : 12 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨12 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block13 :
    ∀ j : Fin 64, ∀ hij : 13 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨13 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block14 :
    ∀ j : Fin 64, ∀ hij : 14 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨14 * 64 + j.1, hij⟩ := by
  simp only [representativeAtProductSignatureRank, productSignatureRank, sortedProductSignature,
    expectedProductSignature, HypercubicDimension16TraceOrbitProductSignatureData.representativeCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?, HypercubicDimension16TraceOrbitProductSignatureData.productSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureData.representativeAtProductSignatureRankCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedProductSignatureRankCodeChunk_eq_table,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedRepresentativeAtProductSignatureRankCodeChunk_eq_table]
  decide +kernel

theorem chunk_rank_tables_block15 :
    ∀ j : Fin 64, ∀ hij : 15 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        representativeAtProductSignatureRank
            (productSignatureRank (chunkIndex localIndex)) =
            chunkIndex localIndex ∧
          sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
            expectedProductSignature (chunkIndex localIndex)
        ) ⟨15 * 64 + j.1, hij⟩ := by
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
    ∀ localIndex : Fin 1024,
      representativeAtProductSignatureRank
          (productSignatureRank (chunkIndex localIndex)) =
          chunkIndex localIndex ∧
        sortedProductSignature (productSignatureRank (chunkIndex localIndex)) =
          expectedProductSignature (chunkIndex localIndex) :=
  HypercubicDimension16DecoderTableRewrite.forall_fin_of_blocks 64 16 (by decide) _
    fun k hk => match k, hk with
      | 0, _ => chunk_rank_tables_block0
      | 1, _ => chunk_rank_tables_block1
      | 2, _ => chunk_rank_tables_block2
      | 3, _ => chunk_rank_tables_block3
      | 4, _ => chunk_rank_tables_block4
      | 5, _ => chunk_rank_tables_block5
      | 6, _ => chunk_rank_tables_block6
      | 7, _ => chunk_rank_tables_block7
      | 8, _ => chunk_rank_tables_block8
      | 9, _ => chunk_rank_tables_block9
      | 10, _ => chunk_rank_tables_block10
      | 11, _ => chunk_rank_tables_block11
      | 12, _ => chunk_rank_tables_block12
      | 13, _ => chunk_rank_tables_block13
      | 14, _ => chunk_rank_tables_block14
      | 15, _ => chunk_rank_tables_block15
      | _ + 16, h => absurd h (by omega)

theorem chunk_sorted_lt_block0 :
    ∀ j : Fin 64, ∀ hij : 0 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨0 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block1 :
    ∀ j : Fin 64, ∀ hij : 1 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨1 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block2 :
    ∀ j : Fin 64, ∀ hij : 2 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨2 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block3 :
    ∀ j : Fin 64, ∀ hij : 3 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨3 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block4 :
    ∀ j : Fin 64, ∀ hij : 4 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨4 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block5 :
    ∀ j : Fin 64, ∀ hij : 5 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨5 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block6 :
    ∀ j : Fin 64, ∀ hij : 6 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨6 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block7 :
    ∀ j : Fin 64, ∀ hij : 7 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨7 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block8 :
    ∀ j : Fin 64, ∀ hij : 8 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨8 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block9 :
    ∀ j : Fin 64, ∀ hij : 9 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨9 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block10 :
    ∀ j : Fin 64, ∀ hij : 10 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨10 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block11 :
    ∀ j : Fin 64, ∀ hij : 11 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨11 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block12 :
    ∀ j : Fin 64, ∀ hij : 12 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨12 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block13 :
    ∀ j : Fin 64, ∀ hij : 13 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨13 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block14 :
    ∀ j : Fin 64, ∀ hij : 14 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨14 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

theorem chunk_sorted_lt_block15 :
    ∀ j : Fin 64, ∀ hij : 15 * 64 + j.1 < 1024,
      (fun localIndex : Fin 1024 =>
        sortedProductSignatureAt (5120 + localIndex.1) <
          sortedProductSignatureAt (5120 + localIndex.1 + 1)
        ) ⟨15 * 64 + j.1, hij⟩ := by
  simp only [sortedProductSignatureAt, sortedProductSignature,
    HypercubicDimension16TraceOrbitProductSignatureData.sortedCanonicalProductSignatureCode?,
    HypercubicDimension16TraceOrbitProductSignatureKernelTables.decodedSortedCanonicalProductSignatureCodeChunk_eq_table]
  decide +kernel

/-- Bounded replay of adjacent strict increase in the sorted table. -/
theorem chunk_sorted_lt :
    ∀ localIndex : Fin 1024,
      sortedProductSignatureAt (5120 + localIndex.1) <
        sortedProductSignatureAt (5120 + localIndex.1 + 1) :=
  HypercubicDimension16DecoderTableRewrite.forall_fin_of_blocks 64 16 (by decide) _
    fun k hk => match k, hk with
      | 0, _ => chunk_sorted_lt_block0
      | 1, _ => chunk_sorted_lt_block1
      | 2, _ => chunk_sorted_lt_block2
      | 3, _ => chunk_sorted_lt_block3
      | 4, _ => chunk_sorted_lt_block4
      | 5, _ => chunk_sorted_lt_block5
      | 6, _ => chunk_sorted_lt_block6
      | 7, _ => chunk_sorted_lt_block7
      | 8, _ => chunk_sorted_lt_block8
      | 9, _ => chunk_sorted_lt_block9
      | 10, _ => chunk_sorted_lt_block10
      | 11, _ => chunk_sorted_lt_block11
      | 12, _ => chunk_sorted_lt_block12
      | 13, _ => chunk_sorted_lt_block13
      | 14, _ => chunk_sorted_lt_block14
      | 15, _ => chunk_sorted_lt_block15
      | _ + 16, h => absurd h (by omega)

end HypercubicDimension16TraceOrbitProductSignatureTableChunk005
end YangMills
end QuantumTheory
end Mettapedia
