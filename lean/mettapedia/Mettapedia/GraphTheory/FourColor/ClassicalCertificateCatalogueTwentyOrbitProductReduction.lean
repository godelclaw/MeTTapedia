import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitKempeClosure
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagContractCompleteness
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitTargetLayerAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProductReduction

open ClassicalCertificateCatalogueTwenty
open ClassicalCertificateCatalogueTwentyOrbitKempeClosure
open ClassicalCertificateCatalogueTwentyOrbitProductData
open ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment
open ClassicalCertificateCatalogueTwentyOrbitProofDagContractCompleteness
open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateContractColorSearch
open ClassicalCertificateFacePartition
open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitProofDagReduction
open ClassicalCertificateOrbitTargetLayerAttachment
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- The old cf020 proof nodes were enumerated by their least closure layer.
These are the cumulative layer boundaries. -/
def twentiethCatalogueOrbitTargetLayer (target : Nat) : Nat :=
  if target < 2551 then 0
  else if target < 3069 then 1
  else if target < 3312 then 2
  else if target < 3459 then 3
  else if target < 3529 then 4
  else if target < 3569 then 5
  else if target < 3591 then 6
  else if target < 3605 then 7
  else if target < 3609 then 8
  else if target < 3611 then 9
  else 10

/-- Every canonical target of the old contract trie occurs in the
corresponding checked layer of the shared response product. -/
theorem twentiethCatalogueOrbitTargetLayer_checker :
    allTargets
      (targetAttachmentBoolean twentiethCatalogueOrbitProofDagCode
        twentiethCatalogueOrbitProductCertificate
          twentiethCatalogueOrbitTargetLayer)
      twentiethCatalogueOrbitProofDagCode.contractTargets = true := by
  rfl

/-- Every checked canonical contract target reaches a genuine ordinary cf020
boundary coloring through the shared response product. -/
theorem twentiethCatalogueOrbitProduct_target_reduces
    (word : List TraceSymbol)
    (htarget : targetBoolean 12 twentiethCatalogueOrbitProofDagCode word =
      true) :
    KempeCoclosure
      (fun otherWord => FiniteHypermap.RingTrace
        (checkedHypermap twentiethCataloguePartitionValid)
          twentiethCatalogueRing (otherWord.map TraceSymbol.toColor))
      word := by
  apply targetBoolean_reduces twentiethCatalogueOrbitProofDagCode
    twentiethCatalogueOrbitProductCertificate
      twentiethCatalogueOrbitTargetLayer _
        twentiethCatalogueOrbitTargetLayer_checker _ word htarget
  intro layer hlayer fixedWord haccepted
  exact twentiethCatalogueOrbit_root_kempeCoclosure_ordinary layer hlayer
    fixedWord haccepted

/-- Every genuine contracted symbolic boundary trace of cf020 reduces through
the shared response product; no recursive rule of the old proof DAG is used. -/
theorem twentiethCatalogueOrbitProduct_contractTrace_reduces
    (word : List TraceSymbol)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCatalogueReductionMetadataValid.partitionValid)
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata)
      (word.map TraceSymbol.toColor)) :
    KempeCoclosure
      (fun otherWord => FiniteHypermap.RingTrace
        (checkedHypermap twentiethCataloguePartitionValid)
          twentiethCatalogueRing (otherWord.map TraceSymbol.toColor))
      word := by
  apply twentiethCatalogueOrbitProduct_target_reduces word
  simpa only [twentiethCatalogueOrbitReductionMetadata_ring_length] using
    twentiethCatalogueOrbitProofDagTarget_of_contractTrace word hcontract

/-- Color-valued form of the cf020 shared-response-product reduction. -/
theorem twentiethCatalogueOrbitProduct_contractRingTrace_reduces
    (boundaryTrace : List Color)
    (hcontract : FiniteHypermap.ContractRingTrace
      (checkedHypermap twentiethCatalogueReductionMetadataValid.partitionValid)
      (contract twentiethCatalogueReductionMetadata)
      (ring twentiethCatalogueReductionMetadata) boundaryTrace) :
    ∃ word : List TraceSymbol,
      word.map TraceSymbol.toColor = boundaryTrace ∧
        KempeCoclosure
          (fun otherWord => FiniteHypermap.RingTrace
            (checkedHypermap twentiethCataloguePartitionValid)
              twentiethCatalogueRing
                (otherWord.map TraceSymbol.toColor))
          word := by
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
    twentiethCatalogueOrbitProduct_contractTrace_reduces word ?_⟩
  simpa only [hword] using hcontract

end ClassicalCertificateCatalogueTwentyOrbitProductReduction

end Mettapedia.GraphTheory.FourColor
