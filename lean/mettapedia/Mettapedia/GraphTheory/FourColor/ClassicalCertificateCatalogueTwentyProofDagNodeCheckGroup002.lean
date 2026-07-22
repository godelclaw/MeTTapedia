import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk016
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk017
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk018
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk019
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk020
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk021
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk022
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk023

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 016
through 023. -/
theorem twentiethCatalogueProofDagNodeGroup002_checker
    (block : Nat) (hlower : 128 ≤ block) (hupper : block < 192) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h16 : block < 136
  · exact twentiethCatalogueProofDagNodeChunk016_checker
      block (by omega) h16
  by_cases h17 : block < 144
  · exact twentiethCatalogueProofDagNodeChunk017_checker
      block (by omega) h17
  by_cases h18 : block < 152
  · exact twentiethCatalogueProofDagNodeChunk018_checker
      block (by omega) h18
  by_cases h19 : block < 160
  · exact twentiethCatalogueProofDagNodeChunk019_checker
      block (by omega) h19
  by_cases h20 : block < 168
  · exact twentiethCatalogueProofDagNodeChunk020_checker
      block (by omega) h20
  by_cases h21 : block < 176
  · exact twentiethCatalogueProofDagNodeChunk021_checker
      block (by omega) h21
  by_cases h22 : block < 184
  · exact twentiethCatalogueProofDagNodeChunk022_checker
      block (by omega) h22
  · exact twentiethCatalogueProofDagNodeChunk023_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
