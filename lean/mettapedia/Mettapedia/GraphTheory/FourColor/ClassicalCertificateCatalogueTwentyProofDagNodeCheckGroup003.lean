import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk024
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk025
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk026
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk027
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk028
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk029
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk030
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk031

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 024
through 031. -/
theorem twentiethCatalogueProofDagNodeGroup003_checker
    (block : Nat) (hlower : 192 ≤ block) (hupper : block < 256) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h24 : block < 200
  · exact twentiethCatalogueProofDagNodeChunk024_checker
      block (by omega) h24
  by_cases h25 : block < 208
  · exact twentiethCatalogueProofDagNodeChunk025_checker
      block (by omega) h25
  by_cases h26 : block < 216
  · exact twentiethCatalogueProofDagNodeChunk026_checker
      block (by omega) h26
  by_cases h27 : block < 224
  · exact twentiethCatalogueProofDagNodeChunk027_checker
      block (by omega) h27
  by_cases h28 : block < 232
  · exact twentiethCatalogueProofDagNodeChunk028_checker
      block (by omega) h28
  by_cases h29 : block < 240
  · exact twentiethCatalogueProofDagNodeChunk029_checker
      block (by omega) h29
  by_cases h30 : block < 248
  · exact twentiethCatalogueProofDagNodeChunk030_checker
      block (by omega) h30
  · exact twentiethCatalogueProofDagNodeChunk031_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
