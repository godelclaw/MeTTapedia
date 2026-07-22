import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock264_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 264 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock265_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 265 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock266_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 266 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock267_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 267 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock268_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 268 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock269_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 269 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock270_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 270 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock271_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 271 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 033. -/
theorem twentiethCatalogueProofDagNodeChunk033_checker
    (block : Nat) (hlower : 264 ≤ block) (hupper : block < 272) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock264_checker, twentiethCatalogueProofDagNodeBlock265_checker, twentiethCatalogueProofDagNodeBlock266_checker, twentiethCatalogueProofDagNodeBlock267_checker, twentiethCatalogueProofDagNodeBlock268_checker, twentiethCatalogueProofDagNodeBlock269_checker, twentiethCatalogueProofDagNodeBlock270_checker, twentiethCatalogueProofDagNodeBlock271_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
