import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock008_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 8 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock009_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 9 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock010_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 10 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock011_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 11 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock012_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 12 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock013_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 13 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock014_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 14 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock015_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 15 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 001. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk001_checker
    (block : Nat) (hlower : 8 ≤ block) (hupper : block < 16) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock008_checker,
      twentiethCatalogueOrbitProofDagNodeBlock009_checker,
      twentiethCatalogueOrbitProofDagNodeBlock010_checker,
      twentiethCatalogueOrbitProofDagNodeBlock011_checker,
      twentiethCatalogueOrbitProofDagNodeBlock012_checker,
      twentiethCatalogueOrbitProofDagNodeBlock013_checker,
      twentiethCatalogueOrbitProofDagNodeBlock014_checker,
      twentiethCatalogueOrbitProofDagNodeBlock015_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
