import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock160_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 160 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock161_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 161 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock162_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 162 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock163_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 163 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock164_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 164 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock165_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 165 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock166_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 166 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock167_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 167 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 020. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk020_checker
    (block : Nat) (hlower : 160 ≤ block) (hupper : block < 168) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock160_checker,
      twentiethCatalogueOrbitProofDagNodeBlock161_checker,
      twentiethCatalogueOrbitProofDagNodeBlock162_checker,
      twentiethCatalogueOrbitProofDagNodeBlock163_checker,
      twentiethCatalogueOrbitProofDagNodeBlock164_checker,
      twentiethCatalogueOrbitProofDagNodeBlock165_checker,
      twentiethCatalogueOrbitProofDagNodeBlock166_checker,
      twentiethCatalogueOrbitProofDagNodeBlock167_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
