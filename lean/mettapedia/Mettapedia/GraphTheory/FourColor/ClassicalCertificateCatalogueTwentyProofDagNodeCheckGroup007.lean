import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk056
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk057
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk058
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk059
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk060
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk061
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk062
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk063

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 056
through 063. -/
theorem twentiethCatalogueProofDagNodeGroup007_checker
    (block : Nat) (hlower : 448 ≤ block) (hupper : block < 512) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h56 : block < 456
  · exact twentiethCatalogueProofDagNodeChunk056_checker
      block (by omega) h56
  by_cases h57 : block < 464
  · exact twentiethCatalogueProofDagNodeChunk057_checker
      block (by omega) h57
  by_cases h58 : block < 472
  · exact twentiethCatalogueProofDagNodeChunk058_checker
      block (by omega) h58
  by_cases h59 : block < 480
  · exact twentiethCatalogueProofDagNodeChunk059_checker
      block (by omega) h59
  by_cases h60 : block < 488
  · exact twentiethCatalogueProofDagNodeChunk060_checker
      block (by omega) h60
  by_cases h61 : block < 496
  · exact twentiethCatalogueProofDagNodeChunk061_checker
      block (by omega) h61
  by_cases h62 : block < 504
  · exact twentiethCatalogueProofDagNodeChunk062_checker
      block (by omega) h62
  · exact twentiethCatalogueProofDagNodeChunk063_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
