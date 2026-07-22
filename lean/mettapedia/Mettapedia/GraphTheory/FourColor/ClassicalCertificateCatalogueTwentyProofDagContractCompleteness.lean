import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearch
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagContractTraceMap

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagContractCompleteness

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagContractTraceMap
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateColorTrace
open ClassicalCertificateContractColorSearch
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateProofDagReduction
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

theorem twentiethCatalogueReductionMetadata_hypermap :
    twentiethCatalogueReductionMetadata.hypermap =
      twentiethCatalogueSampleCode := by
  rfl

theorem twentiethCatalogueReductionMetadata_partition :
    twentiethCatalogueReductionMetadata.partition =
      twentiethCatalogueFacePartition := by
  rfl

theorem twentiethCatalogueReductionMetadata_ring :
    ring twentiethCatalogueReductionMetadata = twentiethCatalogueRing := by
  rfl

theorem twentiethCatalogueReductionMetadata_contract :
    contract twentiethCatalogueReductionMetadata = twentiethCatalogueContract := by
  rfl

theorem twentiethCatalogueReductionMetadata_ring_length :
    (ring twentiethCatalogueReductionMetadata).length = 12 := by
  rfl

/-- Every genuine contracted boundary word of the exact cf020 metadata is a
checked target of its proof DAG. -/
theorem twentiethCatalogueProofDagTarget_of_contractTrace
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCatalogueReductionMetadataValid.partitionValid)
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata)
      (word.map TraceSymbol.toColor)) :
    TargetTreeCode.targetBoolean
      (ring twentiethCatalogueReductionMetadata).length
      twentiethCatalogueProofDagCode word = true := by
  have hcontractOld : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
      twentiethCatalogueContract twentiethCatalogueRing
      (word.map TraceSymbol.toColor) := by
    change FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCataloguePartitionValid)
      twentiethCatalogueContract twentiethCatalogueRing
      (word.map TraceSymbol.toColor) at hcontract
    exact hcontract
  obtain ⟨assignment, hassignment, htrace⟩ :=
    (contractRingTrace_iff_exists_assignment twentiethCataloguePartitionValid
      twentiethCatalogueContract twentiethCatalogueRing _).1 hcontractOld
  have hmember : twentiethCatalogueHasContractTrace word = true := by
    apply twentiethCatalogueContractSearch.acceptsBy_of_contractWord
      twentiethCatalogueComponentsValid twentiethCatalogueRing
      twentiethCatalogueHasContractTrace twentiethCatalogueContractSearch_checker
      twentiethCatalogueRing_reverseBoundaryCycle
      twentiethCatalogueContract_avoidsBoundary assignment hassignment
    exact htrace
  have hlength : word.length = 12 := by
    calc
      word.length = (word.map TraceSymbol.toColor).length := by simp
      _ = (ringTraceOfAssignment twentiethCataloguePartitionValid
          twentiethCatalogueRing assignment).length :=
        congrArg List.length htrace
      _ = 12 := by
        simp [ringTraceOfAssignment, FiniteHypermap.ringColorWord,
          length_trace, twentiethCatalogueRing]
  have htarget := twentiethCatalogueProofDagTarget_of_contractTraceMap
    word hlength (by
      simpa [twentiethCatalogueHasContractTrace] using hmember)
  rw [twentiethCatalogueReductionMetadata_ring_length]
  exact htarget

end ClassicalCertificateCatalogueTwentyProofDagContractCompleteness

end Mettapedia.GraphTheory.FourColor
