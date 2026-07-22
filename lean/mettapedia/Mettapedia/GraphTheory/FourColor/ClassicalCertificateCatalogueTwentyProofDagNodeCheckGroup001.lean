import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk008
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk009
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk010
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk011
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk012
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk013
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk014
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk015

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 008
through 015. -/
theorem twentiethCatalogueProofDagNodeGroup001_checker
    (block : Nat) (hlower : 64 ≤ block) (hupper : block < 128) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h8 : block < 72
  · exact twentiethCatalogueProofDagNodeChunk008_checker
      block (by omega) h8
  by_cases h9 : block < 80
  · exact twentiethCatalogueProofDagNodeChunk009_checker
      block (by omega) h9
  by_cases h10 : block < 88
  · exact twentiethCatalogueProofDagNodeChunk010_checker
      block (by omega) h10
  by_cases h11 : block < 96
  · exact twentiethCatalogueProofDagNodeChunk011_checker
      block (by omega) h11
  by_cases h12 : block < 104
  · exact twentiethCatalogueProofDagNodeChunk012_checker
      block (by omega) h12
  by_cases h13 : block < 112
  · exact twentiethCatalogueProofDagNodeChunk013_checker
      block (by omega) h13
  by_cases h14 : block < 120
  · exact twentiethCatalogueProofDagNodeChunk014_checker
      block (by omega) h14
  · exact twentiethCatalogueProofDagNodeChunk015_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
