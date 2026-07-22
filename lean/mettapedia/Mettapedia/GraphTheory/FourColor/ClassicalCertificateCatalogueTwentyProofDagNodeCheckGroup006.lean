import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk048
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk049
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk050
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk051
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk052
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk053
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk054
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk055

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 048
through 055. -/
theorem twentiethCatalogueProofDagNodeGroup006_checker
    (block : Nat) (hlower : 384 ≤ block) (hupper : block < 448) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h48 : block < 392
  · exact twentiethCatalogueProofDagNodeChunk048_checker
      block (by omega) h48
  by_cases h49 : block < 400
  · exact twentiethCatalogueProofDagNodeChunk049_checker
      block (by omega) h49
  by_cases h50 : block < 408
  · exact twentiethCatalogueProofDagNodeChunk050_checker
      block (by omega) h50
  by_cases h51 : block < 416
  · exact twentiethCatalogueProofDagNodeChunk051_checker
      block (by omega) h51
  by_cases h52 : block < 424
  · exact twentiethCatalogueProofDagNodeChunk052_checker
      block (by omega) h52
  by_cases h53 : block < 432
  · exact twentiethCatalogueProofDagNodeChunk053_checker
      block (by omega) h53
  by_cases h54 : block < 440
  · exact twentiethCatalogueProofDagNodeChunk054_checker
      block (by omega) h54
  · exact twentiethCatalogueProofDagNodeChunk055_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
