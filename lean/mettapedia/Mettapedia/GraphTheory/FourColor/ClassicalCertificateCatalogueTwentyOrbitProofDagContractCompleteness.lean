import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyContractSearch
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagContractCompleteness

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment
open ClassicalCertificateCatalogueTwentyOrbitProofDagContractTraceMap
open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateColorTrace
open ClassicalCertificateContractColorSearch
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

theorem twentiethCatalogueOrbitReductionMetadata_ring_length :
    (ring twentiethCatalogueReductionMetadata).length = 12 := by
  rfl

/-- Every genuine contracted boundary word of the exact cf020 metadata is a
checked target of its color-orbit proof DAG. -/
theorem twentiethCatalogueOrbitProofDagTarget_of_contractTrace
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCatalogueReductionMetadataValid.partitionValid)
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata)
      (word.map TraceSymbol.toColor)) :
    targetBoolean
      (ring twentiethCatalogueReductionMetadata).length
      twentiethCatalogueOrbitProofDagCode word = true := by
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
  have htarget := twentiethCatalogueOrbitProofDagTarget_of_contractTraceMap
    word hlength (by
      simpa [twentiethCatalogueHasContractTrace] using hmember)
  rw [twentiethCatalogueOrbitReductionMetadata_ring_length]
  exact htarget

end ClassicalCertificateCatalogueTwentyOrbitProofDagContractCompleteness

end Mettapedia.GraphTheory.FourColor
