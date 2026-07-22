import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractCompleteness
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagReduction

open ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment
open ClassicalCertificateCatalogueTwentyOrbitProofDagContractCompleteness
open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateContractColorSearch
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

/-- Every contracted symbolic boundary trace of cf020 reaches a genuine
ordinary boundary coloring through the color-orbit proof DAG. -/
theorem twentiethCatalogueOrbitProofDag_contractTrace_reduces
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCatalogueReductionMetadataValid.partitionValid)
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata)
      (word.map TraceSymbol.toColor)) :
    KempeCoclosure
      (OrdinaryTrace twentiethCatalogueReductionMetadataValid) word := by
  apply contractWord_reduces twentiethCatalogueReductionMetadataValid
    twentiethCatalogueOrbitProofDagCode
      twentiethCatalogueOrbitProofDagNode_checker
  exact twentiethCatalogueOrbitProofDagTarget_of_contractTrace word hcontract

/-- Color-valued form of the exact cf020 color-orbit proof-DAG reduction. -/
theorem twentiethCatalogueOrbitProofDag_contractRingTrace_reduces
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCatalogueReductionMetadataValid.partitionValid)
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata) boundaryTrace) :
    ∃ word : List TraceSymbol,
      word.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure
          (OrdinaryTrace twentiethCatalogueReductionMetadataValid) word := by
  obtain ⟨assignment, hassignment, hboundary⟩ :=
    (contractRingTrace_iff_exists_assignment
      twentiethCatalogueReductionMetadataValid.partitionValid
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata) boundaryTrace).1 hcontract
  let word := symbolTraceOfAssignment
    twentiethCatalogueReductionMetadataValid.partitionValid
    (ring twentiethCatalogueReductionMetadata) assignment
  have hword : word.map TraceSymbol.toColor = boundaryTrace := by
    rw [symbolTraceOfAssignment_toColor
      twentiethCatalogueReductionMetadataValid.partitionValid
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata) assignment hassignment
      twentiethCatalogueReductionMetadataValid.reverseBoundaryCycle
      twentiethCatalogueReductionMetadataValid.contractAvoidsBoundary]
    exact hboundary.symm
  refine ⟨word, hword,
    twentiethCatalogueOrbitProofDag_contractTrace_reduces word ?_⟩
  simpa only [hword] using hcontract

end ClassicalCertificateCatalogueTwentyOrbitProofDagReduction

end Mettapedia.GraphTheory.FourColor
