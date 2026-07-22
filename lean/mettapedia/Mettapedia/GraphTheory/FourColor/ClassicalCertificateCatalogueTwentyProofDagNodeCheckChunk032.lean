import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock256_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 256 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock257_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 257 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock258_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 258 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock259_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 259 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock260_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 260 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock261_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 261 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock262_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 262 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock263_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 263 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 032. -/
theorem twentiethCatalogueProofDagNodeChunk032_checker
    (block : Nat) (hlower : 256 ≤ block) (hupper : block < 264) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock256_checker, twentiethCatalogueProofDagNodeBlock257_checker, twentiethCatalogueProofDagNodeBlock258_checker, twentiethCatalogueProofDagNodeBlock259_checker, twentiethCatalogueProofDagNodeBlock260_checker, twentiethCatalogueProofDagNodeBlock261_checker, twentiethCatalogueProofDagNodeBlock262_checker, twentiethCatalogueProofDagNodeBlock263_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
