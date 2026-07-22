import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateCatalogueTwentyProofDagData
open ClassicalCertificateProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueProofDagNodeBlock184_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 184 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock185_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 185 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock186_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 186 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock187_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 187 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock188_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 188 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock189_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 189 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock190_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 190 = true := by
  rfl

theorem twentiethCatalogueProofDagNodeBlock191_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode 191 = true := by
  rfl

/-- The eight semantic blocks backed by node-data chunk 023. -/
theorem twentiethCatalogueProofDagNodeChunk023_checker
    (block : Nat) (hlower : 184 ≤ block) (hupper : block < 192) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueProofDagNodeBlock184_checker, twentiethCatalogueProofDagNodeBlock185_checker, twentiethCatalogueProofDagNodeBlock186_checker, twentiethCatalogueProofDagNodeBlock187_checker, twentiethCatalogueProofDagNodeBlock188_checker, twentiethCatalogueProofDagNodeBlock189_checker, twentiethCatalogueProofDagNodeBlock190_checker, twentiethCatalogueProofDagNodeBlock191_checker]

end ClassicalCertificateCatalogueTwentyProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
