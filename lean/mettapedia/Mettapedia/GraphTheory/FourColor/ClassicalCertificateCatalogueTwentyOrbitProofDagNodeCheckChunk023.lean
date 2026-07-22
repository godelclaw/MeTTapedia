import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock184_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 184 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock185_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 185 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock186_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 186 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock187_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 187 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock188_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 188 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock189_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 189 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock190_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 190 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock191_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 191 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 023. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk023_checker
    (block : Nat) (hlower : 184 ≤ block) (hupper : block < 192) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock184_checker,
      twentiethCatalogueOrbitProofDagNodeBlock185_checker,
      twentiethCatalogueOrbitProofDagNodeBlock186_checker,
      twentiethCatalogueOrbitProofDagNodeBlock187_checker,
      twentiethCatalogueOrbitProofDagNodeBlock188_checker,
      twentiethCatalogueOrbitProofDagNodeBlock189_checker,
      twentiethCatalogueOrbitProofDagNodeBlock190_checker,
      twentiethCatalogueOrbitProofDagNodeBlock191_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
