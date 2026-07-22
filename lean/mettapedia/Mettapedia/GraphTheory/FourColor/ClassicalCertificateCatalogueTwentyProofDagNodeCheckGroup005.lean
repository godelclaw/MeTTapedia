import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk040
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk041
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk042
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk043
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk044
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk045
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk046
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagNodeCheckChunk047

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

/-- The checked node-block interval backed by data chunks 040
through 047. -/
theorem twentiethCatalogueProofDagNodeGroup005_checker
    (block : Nat) (hlower : 320 ≤ block) (hupper : block < 384) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  by_cases h40 : block < 328
  · exact twentiethCatalogueProofDagNodeChunk040_checker
      block (by omega) h40
  by_cases h41 : block < 336
  · exact twentiethCatalogueProofDagNodeChunk041_checker
      block (by omega) h41
  by_cases h42 : block < 344
  · exact twentiethCatalogueProofDagNodeChunk042_checker
      block (by omega) h42
  by_cases h43 : block < 352
  · exact twentiethCatalogueProofDagNodeChunk043_checker
      block (by omega) h43
  by_cases h44 : block < 360
  · exact twentiethCatalogueProofDagNodeChunk044_checker
      block (by omega) h44
  by_cases h45 : block < 368
  · exact twentiethCatalogueProofDagNodeChunk045_checker
      block (by omega) h45
  by_cases h46 : block < 376
  · exact twentiethCatalogueProofDagNodeChunk046_checker
      block (by omega) h46
  · exact twentiethCatalogueProofDagNodeChunk047_checker
      block (by omega) hupper

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
