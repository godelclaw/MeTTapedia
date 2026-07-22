import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk064
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk065
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk066
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk067
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk068
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk069
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk070
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk071

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 064
through 071. -/
theorem twentiethCatalogueProofDagNodeGroup008_checker
    (block : Nat) (hlower : 512 ≤ block) (hupper : block < 576) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h64 : block < 520
  · exact twentiethCatalogueProofDagNodeChunk064_checker
      block (by omega) h64
  by_cases h65 : block < 528
  · exact twentiethCatalogueProofDagNodeChunk065_checker
      block (by omega) h65
  by_cases h66 : block < 536
  · exact twentiethCatalogueProofDagNodeChunk066_checker
      block (by omega) h66
  by_cases h67 : block < 544
  · exact twentiethCatalogueProofDagNodeChunk067_checker
      block (by omega) h67
  by_cases h68 : block < 552
  · exact twentiethCatalogueProofDagNodeChunk068_checker
      block (by omega) h68
  by_cases h69 : block < 560
  · exact twentiethCatalogueProofDagNodeChunk069_checker
      block (by omega) h69
  by_cases h70 : block < 568
  · exact twentiethCatalogueProofDagNodeChunk070_checker
      block (by omega) h70
  · exact twentiethCatalogueProofDagNodeChunk071_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
