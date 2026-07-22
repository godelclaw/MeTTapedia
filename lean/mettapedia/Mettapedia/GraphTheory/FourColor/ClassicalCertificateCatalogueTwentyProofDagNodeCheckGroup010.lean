import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk080
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk081
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk082

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 080
through 082. -/
theorem twentiethCatalogueProofDagNodeGroup010_checker
    (block : Nat) (hlower : 640 ≤ block) (hupper : block < 664) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h80 : block < 648
  · exact twentiethCatalogueProofDagNodeChunk080_checker
      block (by omega) h80
  by_cases h81 : block < 656
  · exact twentiethCatalogueProofDagNodeChunk081_checker
      block (by omega) h81
  · exact twentiethCatalogueProofDagNodeChunk082_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
