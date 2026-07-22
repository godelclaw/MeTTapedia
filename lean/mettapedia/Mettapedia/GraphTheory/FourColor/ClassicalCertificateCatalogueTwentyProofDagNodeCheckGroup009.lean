import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk072
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk073
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk074
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk075
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk076
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk077
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk078
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk079

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 072
through 079. -/
theorem twentiethCatalogueProofDagNodeGroup009_checker
    (block : Nat) (hlower : 576 ≤ block) (hupper : block < 640) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h72 : block < 584
  · exact twentiethCatalogueProofDagNodeChunk072_checker
      block (by omega) h72
  by_cases h73 : block < 592
  · exact twentiethCatalogueProofDagNodeChunk073_checker
      block (by omega) h73
  by_cases h74 : block < 600
  · exact twentiethCatalogueProofDagNodeChunk074_checker
      block (by omega) h74
  by_cases h75 : block < 608
  · exact twentiethCatalogueProofDagNodeChunk075_checker
      block (by omega) h75
  by_cases h76 : block < 616
  · exact twentiethCatalogueProofDagNodeChunk076_checker
      block (by omega) h76
  by_cases h77 : block < 624
  · exact twentiethCatalogueProofDagNodeChunk077_checker
      block (by omega) h77
  by_cases h78 : block < 632
  · exact twentiethCatalogueProofDagNodeChunk078_checker
      block (by omega) h78
  · exact twentiethCatalogueProofDagNodeChunk079_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
