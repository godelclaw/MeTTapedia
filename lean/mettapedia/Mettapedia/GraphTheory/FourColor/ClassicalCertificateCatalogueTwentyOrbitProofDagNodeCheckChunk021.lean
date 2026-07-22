import Mettapedia.GraphTheory.FourColor.ClassicalCertificateCatalogueTwentyOrbitProofDagAttachment

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

open ClassicalCertificateCatalogueTwentyOrbitProofDagData
open ClassicalCertificateCatalogueTwentyProofDagAttachment
open ClassicalCertificateOrbitProofDagReduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem twentiethCatalogueOrbitProofDagNodeBlock168_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 168 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock169_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 169 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock170_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 170 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock171_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 171 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock172_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 172 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock173_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 173 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock174_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 174 = true := by
  rfl

theorem twentiethCatalogueOrbitProofDagNodeBlock175_checker :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode 175 = true := by
  rfl

/-- The eight semantic blocks backed by orbit-node chunk 021. -/
theorem twentiethCatalogueOrbitProofDagNodeChunk021_checker
    (block : Nat) (hlower : 168 ≤ block) (hupper : block < 176) :
    nodeBlockBoolean twentiethCatalogueReductionMetadataValid
      twentiethCatalogueOrbitProofDagCode block = true := by
  interval_cases block <;>
    simp_all only [twentiethCatalogueOrbitProofDagNodeBlock168_checker,
      twentiethCatalogueOrbitProofDagNodeBlock169_checker,
      twentiethCatalogueOrbitProofDagNodeBlock170_checker,
      twentiethCatalogueOrbitProofDagNodeBlock171_checker,
      twentiethCatalogueOrbitProofDagNodeBlock172_checker,
      twentiethCatalogueOrbitProofDagNodeBlock173_checker,
      twentiethCatalogueOrbitProofDagNodeBlock174_checker,
      twentiethCatalogueOrbitProofDagNodeBlock175_checker]

end ClassicalCertificateCatalogueTwentyOrbitProofDagNodeCheck

end Mettapedia.GraphTheory.FourColor
