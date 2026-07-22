import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock008_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 8 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock009_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 9 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock010_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 10 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock011_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 11 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock012_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 12 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock013_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 13 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock014_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 14 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock015_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 15 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 001. -/
theorem twentiethCatalogueProofDagNodeChunk001_checker
    (block : Nat) (hlower : 8 ≤ block) (hupper : block < 16) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock008_checker, twentiethCatalogueProofDagNodeBlock009_checker, twentiethCatalogueProofDagNodeBlock010_checker, twentiethCatalogueProofDagNodeBlock011_checker, twentiethCatalogueProofDagNodeBlock012_checker, twentiethCatalogueProofDagNodeBlock013_checker, twentiethCatalogueProofDagNodeBlock014_checker, twentiethCatalogueProofDagNodeBlock015_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
