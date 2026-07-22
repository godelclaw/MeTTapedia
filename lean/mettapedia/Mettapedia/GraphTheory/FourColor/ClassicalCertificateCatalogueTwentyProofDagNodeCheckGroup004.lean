import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk032
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk033
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk034
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk035
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk036
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk037
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk038
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk039

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 032
through 039. -/
theorem twentiethCatalogueProofDagNodeGroup004_checker
    (block : Nat) (hlower : 256 ≤ block) (hupper : block < 320) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h32 : block < 264
  · exact twentiethCatalogueProofDagNodeChunk032_checker
      block (by omega) h32
  by_cases h33 : block < 272
  · exact twentiethCatalogueProofDagNodeChunk033_checker
      block (by omega) h33
  by_cases h34 : block < 280
  · exact twentiethCatalogueProofDagNodeChunk034_checker
      block (by omega) h34
  by_cases h35 : block < 288
  · exact twentiethCatalogueProofDagNodeChunk035_checker
      block (by omega) h35
  by_cases h36 : block < 296
  · exact twentiethCatalogueProofDagNodeChunk036_checker
      block (by omega) h36
  by_cases h37 : block < 304
  · exact twentiethCatalogueProofDagNodeChunk037_checker
      block (by omega) h37
  by_cases h38 : block < 312
  · exact twentiethCatalogueProofDagNodeChunk038_checker
      block (by omega) h38
  · exact twentiethCatalogueProofDagNodeChunk039_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
