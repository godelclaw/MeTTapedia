import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock016_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 16 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock017_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 17 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock018_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 18 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock019_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 19 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock020_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 20 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock021_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 21 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock022_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 22 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock023_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 23 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 002. -/
theorem twentiethCatalogueProofDagNodeChunk002_checker
    (block : Nat) (hlower : 16 ≤ block) (hupper : block < 24) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock016_checker, twentiethCatalogueProofDagNodeBlock017_checker, twentiethCatalogueProofDagNodeBlock018_checker, twentiethCatalogueProofDagNodeBlock019_checker, twentiethCatalogueProofDagNodeBlock020_checker, twentiethCatalogueProofDagNodeBlock021_checker, twentiethCatalogueProofDagNodeBlock022_checker, twentiethCatalogueProofDagNodeBlock023_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
