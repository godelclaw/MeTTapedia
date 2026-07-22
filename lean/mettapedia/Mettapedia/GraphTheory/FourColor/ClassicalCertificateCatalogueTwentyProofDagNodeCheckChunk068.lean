import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock544_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 544 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock545_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 545 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock546_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 546 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock547_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 547 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock548_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 548 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock549_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 549 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock550_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 550 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock551_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 551 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 068. -/
theorem twentiethCatalogueProofDagNodeChunk068_checker
    (block : Nat) (hlower : 544 ≤ block) (hupper : block < 552) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock544_checker, twentiethCatalogueProofDagNodeBlock545_checker, twentiethCatalogueProofDagNodeBlock546_checker, twentiethCatalogueProofDagNodeBlock547_checker, twentiethCatalogueProofDagNodeBlock548_checker, twentiethCatalogueProofDagNodeBlock549_checker, twentiethCatalogueProofDagNodeBlock550_checker, twentiethCatalogueProofDagNodeBlock551_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
