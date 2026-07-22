import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock016_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 16 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock017_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 17 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock018_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 18 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock019_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 19 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock020_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 20 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock021_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 21 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock022_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 22 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock023_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 23 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 002. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk002_checker
    (block : Nat) (hlower : 16 ≤ block) (hupper : block < 24) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock016_checker,
      twentiethCatalogueOrbitProofDagNodeBlock017_checker,
      twentiethCatalogueOrbitProofDagNodeBlock018_checker,
      twentiethCatalogueOrbitProofDagNodeBlock019_checker,
      twentiethCatalogueOrbitProofDagNodeBlock020_checker,
      twentiethCatalogueOrbitProofDagNodeBlock021_checker,
      twentiethCatalogueOrbitProofDagNodeBlock022_checker,
      twentiethCatalogueOrbitProofDagNodeBlock023_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
