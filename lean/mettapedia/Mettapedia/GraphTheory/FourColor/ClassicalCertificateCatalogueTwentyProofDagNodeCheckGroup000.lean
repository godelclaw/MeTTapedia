import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk000
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk001
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk002
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk003
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk004
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk005
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk006
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk007

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 000
through 007. -/
theorem twentiethCatalogueProofDagNodeGroup000_checker
    (block : Nat) (hlower : 0 ≤ block) (hupper : block < 64) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h0 : block < 8
  · exact twentiethCatalogueProofDagNodeChunk000_checker
      block (by omega) h0
  by_cases h1 : block < 16
  · exact twentiethCatalogueProofDagNodeChunk001_checker
      block (by omega) h1
  by_cases h2 : block < 24
  · exact twentiethCatalogueProofDagNodeChunk002_checker
      block (by omega) h2
  by_cases h3 : block < 32
  · exact twentiethCatalogueProofDagNodeChunk003_checker
      block (by omega) h3
  by_cases h4 : block < 40
  · exact twentiethCatalogueProofDagNodeChunk004_checker
      block (by omega) h4
  by_cases h5 : block < 48
  · exact twentiethCatalogueProofDagNodeChunk005_checker
      block (by omega) h5
  by_cases h6 : block < 56
  · exact twentiethCatalogueProofDagNodeChunk006_checker
      block (by omega) h6
  · exact twentiethCatalogueProofDagNodeChunk007_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
